package tofu.data.calc

import tofu.data.Nothing2T

import scala.annotation.tailrec

trait CalcRunner[-F[+_, +_]] {
  def apply[R, SI, SO, E, A, X](calc: CalcM[F, R, SI, SO, E, A])(r: R, init: SI, cont: Continue[A, E, SO, X]): X

  def runPair[R, SI, SO, E, A](calc: CalcM[F, R, SI, SO, E, A])(r: R, init: SI): (SO, Either[E, A]) = {
    val cont = new Continue[A, E, SO, (SO, Either[E, A])] {
      def success(s: SO, a: A) = (s, Right(a))
      def error(s: SO, e: E)   = (s, Left(e))
    }
    apply(calc)(r, init, cont)
  }
}

object CalcRunner extends LowPriorRunner {
  implicit val nothingRunner: CalcRunner[Nothing] = nothing2TRunner
}

trait LowPriorRunner { self: CalcRunner.type =>
  // scala 2.12 instance for use when Nothing breaks implicit search
  implicit val nothing2TRunner: CalcRunner[Nothing2T] = new CalcRunner[Nothing] {
    @inline private[this] val MaxDepth = 250

    override def apply[R, SI, SO, E, A, X](
        calc: CalcM[Nothing, R, SI, SO, E, A]
    )(r: R, init: SI, cont: Continue[A, E, SO, X]): X = runFast(calc, 0)(r, init, cont)

    def runFastIter[R, SI, SO, E, A, X](
        calc: CalcM[Nothing, R, SI, SO, E, A],
        depth: Int
    )(r: R, init: SI, cont: Continue[A, E, SO, X]): X = runFast(calc, depth + 1)(r, init, cont)

    @tailrec
    def runFast[R, SI, SO, E, A, X](
        calc: CalcM[Nothing, R, SI, SO, E, A],
        depth: Int
    )(r: R, init: SI, cont: Continue[A, E, SO, X]): X = {
      if (depth > MaxDepth) runSlow(calc)(r, init, cont)
      else
        calc match {
          case res: CalcM.CalcMRes[R, SI, SO, E, A]                  => res.submit(r, init, cont)
          case CalcM.Defer(runStep)                                  => runFast(runStep(), depth)(r, init, cont)
          case m: CalcM.ProvideM[Nothing, R, SI, SO, E, A]           => runFast(m.inner, depth)(m.r, init, cont)
          case sub: CalcM.Sub[Nothing, SI, SO, E, A]                 => sub.fa
          case b1: CalcM.Bound[Nothing, R, SI, sm, SO, em, E, am, A] =>
            val cont2 = new Continue[am, em, sm, X] {
              def success(s: sm, a: am): X = runFastIter(b1.continue.success(s, a), depth)(r, s, cont)
              def error(s: sm, e: em): X   = runFastIter(b1.continue.error(s, e), depth)(r, s, cont)
            }
            runFast(b1.src, depth)(r, init, cont2)
        }
    }

    @tailrec
    def runSlow[R, SI, SO, E, A, X](
        calc: CalcM[Nothing, R, SI, SO, E, A]
    )(r: R, init: SI, cont: Continue[A, E, SO, X]): X =
      calc match {
        case res: CalcM.CalcMRes[R, SI, SO, E, A]                  => res.submit(r, init, cont)
        case CalcM.Defer(runStep)                                  => runSlow(runStep())(r, init, cont)
        case m: CalcM.ProvideM[Nothing, R, SI, SO, E, A]           => runSlow(m.inner)(m.r, init, cont)
        case sub: CalcM.Sub[Nothing, SI, SO, E, A]                 => sub.fa
        case b1: CalcM.Bound[Nothing, R, SI, sm, SO, em, E, am, A] =>
          b1.src match {
            case res: CalcM.CalcMRes[_, _, _, _, _]                   =>
              val (st, next) = res.submit(r, init, b1.continue.withState[sm])
              runSlow(next)(r, st, cont)
            case CalcM.Defer(runStep)                                 => runSlow(runStep().bind(b1.continue))(r, init, cont)
            case m: CalcM.ProvideM[Nothing, R, SI, _, _, _]           =>
              type Cont[r] = Continue[am, em, sm, CalcM[Nothing, r, sm, SO, E, A]]
              val kcont = m.any.substitute[Cont](b1.continue)
              runSlow(m.inner.bind(kcont))(m.r, init, cont)
            case sub: CalcM.Sub[Nothing, _, _, _, _]                  => sub.fa
            case b2: CalcM.Bound[Nothing, R, SI, sp, _, ep, _, ap, _] =>
              runSlow(b2.src.bind(Continue.compose(b2.continue, b1.continue)))(r, init, cont)
          }
      }

  }
}
