/*
 * Copyright 2001-2012 Artima, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.scalatest.diagrams

import org.scalactic._
import scala.quoted._
import org.scalatest.{Assertions, DiagrammedExpr}
import org.scalatest.compatible.Assertion

object DiagramsMacro {
  // Transform the input expression by parsing out the anchor and generate expression that can support diagram rendering
  def parse(using QuoteContext)(expr: qctx.reflect.Term): qctx.reflect.Term = {
    import qctx.reflect._
    import util._
    import ValDef.let

    expr.tpe.asType match {
      case '[r] =>
        def isXmlSugar(apply: Apply): Boolean = apply.tpe <:< TypeRepr.of[scala.xml.Elem]
        def isJavaStatic(tree: Tree): Boolean = tree.symbol.flags.is(Flags.Static)
        def isImplicitMethodType(tp: TypeRepr): Boolean = tp match {
          case tp: MethodType => tp.isImplicit
          case _ => false
        }

        def selectField(o: Term, name: String): Term = Select.unique(o, name)

        def default(term: Term): Term = term.asExpr match {
          case '{ $x: t } => Term.of('{ DiagrammedExpr.simpleExpr[t]($x, ${ getAnchor(term) } ) })
        }

        def getAnchorForSelect(sel: Select): Expr[Int] = {
          if (sel.name == "unary_!")
            Expr(sel.pos.startColumn - Position.ofMacroExpansion.startColumn)
          else {
            val selOffset = sel.pos.endColumn - sel.qualifier.pos.endColumn - sel.name.length
            Expr(sel.qualifier.pos.endColumn + selOffset - Position.ofMacroExpansion.startColumn)
          }
        }

        def getAnchor(expr: Term): Expr[Int] = {
          // -1 to match scala2 position
          // Expr((Term.of(expr).pos.endColumn + Term.of(expr).pos.startColumn - 1) / 2 - Position.ofMacroExpansion.startColumn)
          Expr(expr.pos.startColumn - Position.ofMacroExpansion.startColumn)
        }

        def handleArgs(argTps: List[TypeRepr], args: List[Term]): (List[Term], List[Term]) =
          args.zip(argTps).foldLeft(Nil -> Nil : (List[Term], List[Term])) { case ((diagrams, others), pair) =>
            pair match {
              case (arg, ByNameType(_)) =>
                (diagrams, others :+ arg)
              case (arg, tp) =>
                if (tp.widen.typeSymbol.show.startsWith("scala.Function")) (diagrams, others :+ arg)
                else (diagrams :+ parse(arg), others)
            }
          }

        expr match {
          case Apply(Select(New(_), _), _) => default(expr)

          case apply: Apply if isXmlSugar(apply) => default(expr)

          case apply: Apply if isJavaStatic(apply) => default(expr)

          case Select(This(_), _) => default(expr)

          case x: Select if x.symbol.flags.is(Flags.Object) => default(expr)

          case x: Select if isJavaStatic(x) => default(expr)

          case sel @ Select(qual, name) =>
            parse(qual).asExpr match {
              case '{ $obj: DiagrammedExpr[t] } =>
                val anchor = getAnchorForSelect(sel)
                Term.of('{
                  val o = $obj
                  DiagrammedExpr.selectExpr[r](o, ${ selectField(Term.of('{o.value}), name).asExprOf[r] }, $anchor)
                })
            }

          case Block(stats, expr) =>
            // call parse recursively using the expr argument if it is a block
            Block(stats, parse(expr))
          case Apply(sel @ Select(lhs, op), rhs :: Nil) =>
            val anchor = getAnchorForSelect(sel)
            op match {
              case "||" | "|" =>
                val left = parse(lhs).asExprOf[DiagrammedExpr[Boolean]]
                val right = parse(rhs).asExprOf[DiagrammedExpr[Boolean]]

                Term.of('{
                  val l = $left
                  if (l.value) l
                  else {
                    val r = $right
                    DiagrammedExpr.applyExpr[Boolean](l, r :: Nil, r.value, $anchor)
                  }
                })
              case "&&" | "&" =>
                val left = parse(lhs).asExprOf[DiagrammedExpr[Boolean]]
                val right = parse(rhs).asExprOf[DiagrammedExpr[Boolean]]
                Term.of('{
                  val l = $left
                  if (!l.value) l
                  else {
                    val r = $right
                    DiagrammedExpr.applyExpr[Boolean](l, r :: Nil, r.value, $anchor)
                  }
                })
              case _ =>
                val left = parse(lhs)

                val methTp = sel.tpe.widen.asInstanceOf[MethodType]
                val (diagrams, others) = handleArgs(methTp.paramTypes, rhs :: Nil)

                let(left) { l =>
                  let(diagrams) { rs =>
                    l.asExpr match {
                      case '{ $left: DiagrammedExpr[t] } =>
                        val rights = rs.map(_.asExprOf[DiagrammedExpr[_]])
                        val res = Select.unique(l, "value").select(sel.symbol).appliedToArgs(diagrams.map(r => Select.unique(r, "value")) ++ others).asExprOf[r]
                        Term.of('{ DiagrammedExpr.applyExpr[r]($left, ${Expr.ofList(rights)}, $res, $anchor) })
                    }
                  }
                }
            }

          case Apply(sel @ Select(lhs, op), args) =>
            val left = parse(lhs)
            val anchor = getAnchorForSelect(sel)

            val methTp = sel.tpe.widen.asInstanceOf[MethodType]
            val (diagrams, others) = handleArgs(methTp.paramTypes, args)

            let(left) { l =>
              let(diagrams) { rs =>
                l.asExpr match {
                  case '{ $left: DiagrammedExpr[t] } =>
                    val rights = rs.map(_.asExprOf[DiagrammedExpr[_]])
                    val res = Select.unique(l, "value").select(sel.symbol).appliedToArgs(diagrams.map(r => Select.unique(r, "value")) ++ others).asExprOf[r]
                    Term.of('{ DiagrammedExpr.applyExpr[r]($left, ${Expr.ofList(rights)}, $res, $anchor) })
                }
              }
            }

          case Apply(f @ Apply(sel @ Select(Apply(qual, lhs :: Nil), op @ ("===" | "!==")), rhs :: Nil), implicits)
          if isImplicitMethodType(f.tpe) =>
            val left = parse(lhs)
            val right = parse(rhs)
            val anchor = getAnchorForSelect(sel)

            let(left) { left =>
              let(right) { right =>
                val app = qual.appliedTo(Select.unique(left, "value")).select(sel.symbol)
                              .appliedTo(Select.unique(right, "value")).appliedToArgs(implicits)
                let(app) { result =>
                  val l = left.asExprOf[DiagrammedExpr[_]]
                  val r = right.asExprOf[DiagrammedExpr[_]]
                  val b = result.asExprOf[Boolean]
                  Term.of('{ DiagrammedExpr.applyExpr[Boolean]($l, $r :: Nil, $b, $anchor) })
                }
              }
            }

          case Apply(fun @ TypeApply(sel @ Select(lhs, op), targs), args) =>
            val left = parse(lhs)
            val anchor = getAnchorForSelect(sel)

            val methTp = fun.tpe.widen.asInstanceOf[MethodType]
            val (diagrams, others) = handleArgs(methTp.paramTypes, args)

            let(left) { l =>
              let(diagrams) { rs =>
                l.asExpr match {
                  case '{ $left: DiagrammedExpr[t] } =>
                    val rights = rs.map(_.asExprOf[DiagrammedExpr[_]])
                    val res = Select.unique(l, "value").select(sel.symbol).appliedToTypes(targs.map(_.tpe))
                                    .appliedToArgs(diagrams.map(r => Select.unique(r, "value")) ++ others).asExprOf[r]
                    Term.of('{ DiagrammedExpr.applyExpr[r]($left, ${Expr.ofList(rights)}, $res, $anchor) })
                }
              }
            }

          case TypeApply(sel @ Select(lhs, op), targs) =>
            val left = parse(lhs)
            val anchor = getAnchorForSelect(sel)

            let(left) { l =>
              l.asExpr match {
                case '{ $left: DiagrammedExpr[t] } =>
                  val res = Select.unique(l, "value").select(sel.symbol).appliedToTypes(targs.map(_.tpe)).asExprOf[r]
                  Term.of('{ DiagrammedExpr.applyExpr[r]($left, Nil, $res, $anchor) })
              }
            }

          case _ =>
            default(expr)
        }
    }
  }

  def transform(
    helper: Expr[(DiagrammedExpr[Boolean], Any, String, source.Position) => Assertion],
    condition: Expr[Boolean], pos: Expr[source.Position], clue: Expr[Any], sourceText: String
  )(using QuoteContext): Expr[Assertion] = {
    import qctx.reflect._
    val diagExpr = parse(Term.of(condition).underlyingArgument).asExprOf[DiagrammedExpr[Boolean]]
    '{ $helper($diagExpr, $clue, ${Expr(sourceText)}, $pos) }
  }
}