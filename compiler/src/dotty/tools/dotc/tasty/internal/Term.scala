package dotty.tools.dotc.tasty
package internal

import dotty.tools.dotc.ast.Trees.NamedArg
import dotty.tools.dotc.ast.{Trees, tpd}
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.NameKinds._
import dotty.tools.dotc.core.Names

import scala.tasty.statements
import scala.tasty.terms
import scala.tasty.types

object Term {

  def apply(arg: tpd.Tree)(implicit ctx: Context): terms.Term = Impl(arg, ctx)

  def unapplyIdent(arg: statements.TopLevelStatement): Option[terms.Ident.Data] = arg match {
    case Impl(id@Trees.Ident(name: Names.TermName), _) if id.isTerm => Some(TermName(name))
    case _ => None
  }

  def unapplySelect(arg: statements.TopLevelStatement): Option[terms.Select.Data] = arg match {
    case Impl(id@Trees.Select(qual, name: Names.TermName), ctx) if id.isTerm => Some(Term(qual)(ctx), TermName(name))
    case _ => None
  }

  def unapplyLiteral(arg: statements.TopLevelStatement): Option[terms.Literal.Data] = arg match {
    case Impl(Trees.Literal(const), _) => Some(Constant(const))
    case _ => None
  }

  def unapplyThis(arg: statements.TopLevelStatement): Option[terms.This.Data] = arg match {
    case Impl(Trees.This(qual), ctx) => Some(if (qual.isEmpty) None else Some(Id(qual)(ctx)))
    case _ => None
  }

  def unapplyNew(arg: statements.TopLevelStatement): Option[terms.New.Data] = arg match {
    case Impl(Trees.New(tpt), ctx) => Some(TypeTree(tpt)(ctx))
    case _ => None
  }

  def unapplyNamedArg(arg: statements.TopLevelStatement): Option[terms.NamedArg.Data] = arg match {
    case Impl(Trees.NamedArg(name: Names.TermName, arg), ctx) => Some(TermName(name), Term(arg)(ctx))
    case _ => None
  }

  def unapplyApply(arg: statements.TopLevelStatement): Option[terms.Apply.Data] = arg match {
    case Impl(Trees.Apply(fn, args), ctx) => Some((Term(fn)(ctx), args.map(arg => Term(arg)(ctx))))
    case _ => None
  }

  def unapplyTypeApply(arg: statements.TopLevelStatement): Option[terms.TypeApply.Data] = arg match {
    case Impl(Trees.TypeApply(fn, args), ctx) => Some((Term(fn)(ctx), args.map(arg => TypeTree(arg)(ctx))))
    case _ => None
  }

  def unapplySuper(arg: statements.TopLevelStatement): Option[terms.Super.Data] = arg match {
    case Impl(Trees.Super(qual, mixin), ctx) => Some((Term(qual)(ctx), if (mixin.isEmpty) None else Some(Id(mixin)(ctx))))
    case _ => None
  }

  def unapplyTyped(arg: statements.TopLevelStatement): Option[terms.Typed.Data] = arg match {
    case Impl(Trees.Typed(expr, tpt), ctx) => Some((Term(expr)(ctx), TypeTree(tpt)(ctx)))
    case _ => None
  }

  def unapplyAssign(arg: statements.TopLevelStatement): Option[terms.Assign.Data] = arg match {
    case Impl(Trees.Assign(lhs, rhs), ctx) => Some((Term(lhs)(ctx), Term(rhs)(ctx)))
    case _ => None
  }

  def unapplyBlock(arg: statements.TopLevelStatement): Option[terms.Block.Data] = arg match {
    case Impl(Trees.Block(stats, expr), ctx) => Some((stats.map(stat => Statement(stat)(ctx)), Term(expr)(ctx)))
    case _ => None
  }

  def unapplyInlined(arg: statements.TopLevelStatement): Option[terms.Inlined.Data] = arg match {
    case Impl(Trees.Inlined(call, bindings, expansion), ctx) => Some((Term(call)(ctx), bindings.map(Definition(_)(ctx)), Term(expansion)(ctx)))
    case _ => None
  }

  def unapplyLambda(arg: statements.TopLevelStatement): Option[terms.Lambda.Data] = arg match {
    case Impl(Trees.Closure(_, meth, tpt), ctx) => Some((Term(meth)(ctx), if (tpt.isEmpty) None else Some(TypeTree(tpt)(ctx))))
    case _ => None
  }

  def unapplyIf(arg: statements.TopLevelStatement): Option[terms.If.Data] = arg match {
    case Impl(Trees.If(cond, thenp, elsep), ctx) => Some((Term(cond)(ctx), Term(thenp)(ctx), Term(elsep)(ctx)))
    case _ => None
  }

  def unapplyMatch(arg: statements.TopLevelStatement): Option[terms.Match.Data] = arg match {
    case Impl(Trees.Match(selector, cases), ctx) => Some((Term(selector)(ctx), cases.map(c => CaseDef(c)(ctx))))
    case _ => None
  }

  def unapplyTry(arg: statements.TopLevelStatement): Option[terms.Try.Data] = arg match {
    case Impl(Trees.Try(body, catches, finalizer), ctx) => Some((Term(body)(ctx), catches.map(c => CaseDef(c)(ctx)), if (finalizer.isEmpty) None else Some(Term(finalizer)(ctx))))
    case _ => None
  }

  def unapplyReturn(arg: statements.TopLevelStatement): Option[terms.Return.Data] = arg match {
    case Impl(Trees.Return(expr, from), ctx) => Some(Term(expr)(ctx)) // TODO use `from` or remove it
    case _ => None
  }

  def unapplyRepeated(arg: statements.TopLevelStatement): Option[terms.Repeated.Data] = arg match {
    case Impl(Trees.SeqLiteral(args, elemtpt), ctx) => Some(args.map(arg => Term(arg)(ctx))) // TODO use `elemtpt`?
    case _ => None
  }

  def unapplySelectOuter(arg: statements.TopLevelStatement): Option[terms.SelectOuter.Data] = arg match {
    case Impl(sel@Trees.Select(qual, OuterSelectName(_, levels)), ctx) => Some((Term(qual)(ctx), levels, Type(sel.tpe)(ctx)))
    case _ => None
  }

  private case class Impl(tree: tpd.Tree, ctx: Context) extends terms.Term with Positioned {

    assert(tree.isTerm || tree.isInstanceOf[Trees.NamedArg[_]])

    def tpe: types.Type = Type(tree.tpe)(ctx)

    override def toString: String = {
      import Toolbox.extractor
      this match {
        case terms.Ident(name) => s"Ident($name)"
        case terms.Select(qual, name) => s"Select($qual, $name)"
        case terms.Literal(const) => s"Literal($const)"
        case terms.This(id) => s"This($id)"
        case terms.New(tpt) => s"New($tpt)"
        case terms.NamedArg(name, arg) => s"NamedArg($name, $arg)"
        case terms.Apply(fn, args) => s"Apply($fn, ${list(args)})"
        case terms.TypeApply(fn, args) => s"TypeApply($fn, ${list(args)})"
        case terms.Super(qual, mixin) => s"Super($qual, $mixin)"
        case terms.Typed(expr, tpt) => s"Typed($expr, $tpt)"
        case terms.Assign(lhs, rhs) => s"Assign($lhs, $rhs)"
        case terms.Block(stats, expr) => s"Block(${list(stats)}, $expr)"
        case terms.Inlined(call, bindings, expr) => s"Inlined($call, $bindings, $expr)"
        case terms.Lambda(meth, tpt) => s"Lambda($meth, $tpt)"
        case terms.If(cond, thenp, elsep) => s"If($cond, $thenp, $elsep)"
        case terms.Match(selector, cases) => s"Match($selector, ${list(cases)})"
        case terms.Try(body, catches, finalizer) => s"Try($body, ${list(catches)}, $finalizer)"
        case terms.Return(expr) => s"Return($expr)"
        case terms.Repeated(args) => s"Repeated($args)"
        case terms.SelectOuter(from, levels, target) => s"SelectOuter($from, $levels, $target)"
      }
    }

    private def list(xs: List[_]): String =
      if (xs.isEmpty) "Nil" else xs.mkString("List(", ", ", ")")
  }
}
