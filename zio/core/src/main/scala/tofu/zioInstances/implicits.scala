package tofu.zioInstances
import java.io.IOException

import tofu.optics.{Contains, Extract}
import zio.clock.Clock
import zio.console.Console
import zio.random.Random
import zio.{Has, Tag}

object implicits extends ZioTofuImplicits1

private[zioInstances] class ZioTofuImplicits1 extends ZioTofuImplicits2 {
  @inline final implicit def rioTofuImplicit[R]: RioTofuInstance[R] = rioTofuInstance

  @inline final implicit def zioTofuErrorsToImplicit[R, E]: ZioTofuErrorsToInstance[R, E, Nothing] =
    zioTofuErrorsToInstance

  @inline final implicit def zioTofuErrorsExtractToImplicit[R, E, E1: * Extract E]: ZioTofuErrorsToInstance[R, E, E1] =
    zioTofuExtractErrorsInstance

  @inline final implicit def zioTofuTimeoutImplicit[R <: Clock, E]: ZioTofuTimeoutInstance[R, E] =
    zioTofuTimeoutInstance

  @inline final implicit def zioTofuConcurrentImplicit[R1, E1, R, E]: ZioTofuConcurrentInstance[R1, E1, R, E] =
    zioTofuConcurrentInstance

  @inline final implicit def zioTofuConsoleImplicit[R <: Console, E >: IOException]: ZioTofuConsoleInstance[R, E] =
    zioTofuConsoleInstance

  @inline final implicit def zioTofuRandomImplicit[R <: Random, E]: ZioTofuRandomInstance[R, E] = zioTofuRandomInstance

  @inline final implicit def zioTofuContainsUnliftImplicit[R1, R2: * Contains R1, E]
      : ZioTofuContainsUnliftInstance[R1, R2, E] =
    zioTofuContainsUnliftInstance[R1, R2, E]

  @inline final implicit def rioTofuUnliftIOImplicit[R]: RioTofuUnliftIOInstance[R] = rioTofuUnliftIOInstance

}
private[zioInstances] trait ZioTofuImplicits2 extends ZioTofuImplicits3 {
  @inline final implicit def zioTofuImplicit[R, E]: ZioTofuInstance[R, E]               = zioTofuInstance
  @inline final implicit def zioTofuWithRunImplicit[R, E]: ZioTofuWithRunInstance[R, E] = zioTofuWithRunInstance
}

private[zioInstances] trait ZioTofuImplicits3 {
  @inline final implicit def zioTofuUnliftHasImplicit[R <: Has[_], E, C: Tag]: ZioTofuUnliftHasInstance[R, E, C] =
    zioTofuUnliftHasInstance
}
