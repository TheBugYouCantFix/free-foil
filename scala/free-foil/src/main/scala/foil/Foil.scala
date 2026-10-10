package foil

import scala.collection.immutable.IntMap

object Foil {
  type Id = Int
  type RawName = Id
  type RawScope = Set[RawName]
  
  val rawEmptyScope: RawScope = Set.empty[RawName]

  def rawFreshName(rawScope: RawScope): RawName =
    if (rawScope.isEmpty) 0
    else rawScope.max match {
      case m if m == Int.MaxValue => throw new Exception("rawFreshName: name space exhausted")
      case m                      => math.max(0, m + 1)
    }

  def rawExtendScope(rawName: RawName, rawScope: RawScope): RawScope =
    rawScope + rawName

  def rawMember(rawName: RawName)(rawScope: RawScope): Boolean =
    rawScope.contains(rawName)

  case class RawSubst[A](rawMap: IntMap[A])

  def rawIdSubst[A] = IntMap.empty[A]

  def rawLookup[A](rawSubst: RawSubst[A])(rawName: RawName): Option[A] =
    rawSubst.rawMap.get(rawName)

  def rawExtendSubst[A](rawName: RawName, value: A, rawSubst: RawSubst[A]): RawSubst[A] =
    RawSubst(rawSubst.rawMap.updated(rawName, value))

  sealed trait S
  case class VoidS() extends S

  case class Name[N <: S](unsafeName: RawName)
  case class Scope[N <: S](unsafeScope: RawScope)

  val emptyScope = Scope[VoidS](rawEmptyScope)

  def member[L <: S, N <: S](name: Name[L])(scope: Scope[N]): Boolean =
    rawMember(name.unsafeName)(scope.unsafeScope)

  case class NameBinder[N <: S, L <: S](unsafeBinder: Name[L])

  def nameOf[N <: S, L <: S](nameBinder: NameBinder[N, L]): Name[L] =
    nameBinder.unsafeBinder

  def withFreshBinder[N <: S, R](scope: Scope[N])(cont: [L <: S] => NameBinder[N, L] => R): R =
    cont(NameBinder(Name(rawFreshName(scope.unsafeScope))))

  class Distinct[N <: S]
  class ExtEndo[N <: S]
  class Ext[N <: S, L <: S](implicit ev: ExtEndo[N] <:< ExtEndo[L])

  type DExt[N <: S, L <: S] = (Distinct[L], Ext[N, L])

  sealed trait DistinctEvidence[N <: S]
  case object Distinct extends DistinctEvidence[VoidS]
  val unsafeDistinct: DistinctEvidence[VoidS] = Distinct

  sealed trait ExtEvidence[N <: S, L <: S]
  case object Ext extends ExtEvidence[VoidS, VoidS]
  val unsafeExt: ExtEvidence[VoidS, VoidS] = Ext

  trait InjectName[E[_ <: S]] {
    def injectName[N <: S]: Name[N] => E[N]
  }

  case class Substitution[E[_ <: S], I <: S, O <: S](env: IntMap[E[O]])

  trait Sinkable[E[_ <: S]] {
    def sinkabilityProof[N <: S, L <: S](rename: Name[N] => Name[L]): E[N] => E[L]
  }

  object Sinkable {
    given nameSinkable: Sinkable[Name] with {
      def sinkabilityProof[N <: S, L <: S](rename: Name[N] => Name[L]): Name[N] => Name[L] = rename
    }
    given substitutionSinkable[E[_ <: S], I <: S](
        using sinkable: Sinkable[E]
    ): Sinkable[[O <: S] =>> Substitution[E, I, O]] with {
      def sinkabilityProof[N <: S, L <: S](
          rename: Name[N] => Name[L]
      ): Substitution[E, I, N] => Substitution[E, I, L] =
        substitution => Substitution(
          substitution.env.map { case (k, e) => (k, sinkable.sinkabilityProof(rename)(e)) }
        )
    }
  }

  def sink[E[_ <: S]: Sinkable, N <: S, L <: S](en: E[N])(using ev: DExt[N, L]): E[L] = en.asInstanceOf[E[L]]

  def unsafeAssertFresh[N <: S, L <: S, N1 <: S, L1 <: S, R](
      binder: NameBinder[N, L],
  )(cont: DExt[N1, L1] ?=> NameBinder[N1, L1] => R): R = {
    given DExt[N1, L1] = (unsafeDistinct.asInstanceOf[Distinct[L1]], unsafeExt.asInstanceOf[Ext[N1, L1]])
    cont(binder.asInstanceOf[NameBinder[N1, L1]])
  }

  def withFresh[N <: S: Distinct, R](scope: Scope[N])(cont: [L <: S] => DExt[N, L] ?=> NameBinder[N, L] => R): R = {
    withFreshBinder[N, R](scope)([L <: S] => (binder: NameBinder[N, L]) => unsafeAssertFresh(binder)(cont[L]))
  }

  def withRefreshed[O <: S, I <: S, R](scope: Scope[O], name: Name[I])(
      cont: [O1 <: S] => DExt[O, O1] ?=> NameBinder[O, O1] => R,
  ): R = {

    given Distinct[O] = unsafeDistinct.asInstanceOf[Distinct[O]]
    given DExt[O, O]  = (unsafeDistinct.asInstanceOf[Distinct[O]], unsafeExt.asInstanceOf[Ext[O, O]])
    if (member(name)(scope))
      withFresh(scope)(cont)
    else
      unsafeAssertFresh[O, I, O, I, R](NameBinder[O, I](name))(cont[I])
  }

  def extendScope[N <: S, L <: S](nameBinder: NameBinder[N, L], scope: Scope[N]): Scope[L] =
    Scope[L](rawExtendScope(nameBinder.unsafeBinder.unsafeName, scope.unsafeScope))

  def lookupSubst[E[_ <: S]: InjectName, I <: S, O <: S](
      subst: Substitution[E, I, O],
      name: Name[I],
  ): E[O] =
    subst.env.get(name.unsafeName) match
      case Some(e) => e
      case None    => summon[InjectName[E]].injectName(Name(name.unsafeName))

  def identitySubst[E[_ <: S], I <: S]: Substitution[E, I, I] =
    Substitution(IntMap.empty)

  def addSubst[E[_ <: S], I <: S, I1 <: S, O <: S](
      s: Substitution[E, I, O],
      b: NameBinder[I, I1],
      e: E[O],
  ): Substitution[E, I1, O] =
    Substitution(s.env.updated(b.unsafeBinder.unsafeName, e))

  def addRename[E[_ <: S]: InjectName, I <: S, I1 <: S, O <: S](
      s: Substitution[E, I, O],
      b: NameBinder[I, I1],
      n: Name[O],
  ): Substitution[E, I1, O] =
    if (b.unsafeBinder.unsafeName == n.unsafeName)
      Substitution(s.env - b.unsafeBinder.unsafeName)
    else
      addSubst(s, b, summon[InjectName[E]].injectName[O](n))
}
