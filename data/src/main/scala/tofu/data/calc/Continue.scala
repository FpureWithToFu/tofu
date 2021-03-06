package tofu.data.calc

trait Continue[-A, -E, +C] { self =>
  def success(a: A): C
  def error(e: E): C

  def map[D](f: C => D): Continue[A, E, D] = new Continue[A, E, D] {
    override def success(a: A): D = f(self.success(a))
    override def error(e: E): D   = f(self.error(e))
  }
}

object Continue {
  def apply[A, E, X](f: A => X, h: E => X): Continue[A, E, X] = new Continue[A, E, X] {
    override def success(a: A): X = f(a)
    override def error(e: E): X   = h(e)
  }

  def compose[A, B, C, E, V, W, R, S1, S2, S3, F[+_, +_]](
      c1: Continue[A, E, CalcM[F, R, S1, S2, V, B]],
      c2: Continue[B, V, CalcM[F, R, S2, S3, W, C]]
  ): Continue[A, E, CalcM[F, R, S1, S3, W, C]] =
    new Continue[A, E, CalcM[F, R, S1, S3, W, C]] {
      def success(a: A): CalcM[F, R, S1, S3, W, C] = c1.success(a).bind(c2)
      def error(e: E): CalcM[F, R, S1, S3, W, C]   = c1.error(e).bind(c2)
    }

  def flatMapConst[A, E, S, X >: CalcM[Nothing, Any, S, S, E, Nothing]](f: A => X): Continue[A, E, X] =
    new Continue[A, E, X] {
      def success(a: A): X = f(a)
      def error(e: E): X   = CalcM.Raise[S, E](e)
    }

  def handleWithConst[A, E, S, X >: CalcM[Nothing, Any, S, S, Nothing, A]](f: E => X): Continue[A, E, X] =
    new Continue[A, E, X] {
      def success(a: A): X = CalcM.Pure[S, A](a)
      def error(e: E): X   = f(e)
    }

  def swap[A, E, S, X >: CalcM[Nothing, Any, S, S, A, E]]: Continue[A, E, X] =
    new Continue[A, E, X] {
      override def success(a: A): X = CalcM.Raise(a)
      override def error(e: E): X   = CalcM.Pure(e)
    }

  def update[A, E, SI, SO, X >: CalcM[Nothing, Any, SI, SO, E, A]](f: SI => SO): Continue[A, E, X] =
    new Continue[A, E, X] {
      override def success(a: A): X = CalcM.update(f) as_ a
      override def error(e: E): X   = CalcM.update(f).swap errorAs_ e
    }
}
