package languages

import foil.Foil._

object LambdaCalculus {
  sealed trait Expr[N <: S]
  case class VarE[N <: S](name: Name[N])                                   extends Expr[N]
  case class AppE[N <: S](fun: Expr[N], arg: Expr[N])                      extends Expr[N]
  case class LamE[N <: S, L <: S](binder: NameBinder[N, L], body: Expr[L]) extends Expr[N]

  object Expr {
    given exprSinkable: Sinkable[Expr] with {
      def sinkabilityProof[N <: S, L <: S](rename: Name[N] => Name[L]): Expr[N] => Expr[L] = {
        case VarE(v)    => VarE(rename(v))
        case AppE(f, e) => AppE(sinkabilityProof(rename)(f), sinkabilityProof(rename)(e))
        case LamE(binder, body) =>
          val binderInner = binder.asInstanceOf[NameBinder[L, L]]
          val bodyInner   = body.asInstanceOf[Expr[L]]
          val renameInner = rename.asInstanceOf[Name[L] => Name[L]]
          LamE(binderInner, sinkabilityProof(renameInner)(bodyInner))
      }
    }

    given injectName: InjectName[Expr] with {
      def injectName[N <: S]: Name[N] => Expr[N] = VarE.apply
    }

    def substitute[O <: S, I <: S]
      (scope: Scope[O], subst: Substitution[Expr, I, O], expr: Expr[I]): Expr[O] = expr match {
      case VarE(name) => lookupSubst(subst, name)
      case AppE(f, x) => AppE(substitute(scope, subst, f), substitute(scope, subst, x))
      case LamE(binder, body) => withRefreshed(scope, nameOf(binder))
        { [O1 <: S] => implicit dext: DExt[O, O1] => (binder_ : NameBinder[O, O1]) =>
          val subst_ = addRename(sink(subst), binder, nameOf(binder_))
          val scope_ = extendScope(binder_, scope)
          val body_ = substitute(scope_, subst_, body)
          LamE(binder_, body_)
      }
    }
  }
}