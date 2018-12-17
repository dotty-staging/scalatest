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
package org.scalatest

import org.scalactic._
import scala.quoted._
import scala.tasty._

/**
 * Macro implementation that provides rich error message for boolean expression assertion.
 */
object AssertionsMacro {
  /**
   * Provides assertion implementation for <code>Assertions.assert(booleanExpr: Boolean)</code>, with rich error message.
   *
   * @param condition original condition expression
   * @return transformed expression that performs the assertion check and throw <code>TestFailedException</code> with rich error message if assertion failed
   */
  def assert(condition: Expr[Boolean], prettifier: Expr[Prettifier], pos: Expr[source.Position], clue: Expr[Any])(implicit refl: Reflection): Expr[Assertion] =
    transform('(Assertions.assertionsHelper.macroAssert), condition, prettifier, pos, clue)

  /**
   * Provides implementation for <code>Assertions.assume(booleanExpr: Boolean)</code>, with rich error message.
   *
   * @param context macro context
   * @param condition original condition expression
   * @return transformed expression that performs the assumption check and throw <code>TestCanceledException</code> with rich error message if assumption failed
   */
  def assume(condition: Expr[Boolean], prettifier: Expr[Prettifier], pos: Expr[source.Position], clue: Expr[Any])(implicit refl: Reflection): Expr[Assertion] =
    transform('(Assertions.assertionsHelper.macroAssume), condition, prettifier, pos, clue)

  private def transform(
    helper:Expr[(Bool, Any, source.Position) => Assertion],
    condition: Expr[Boolean], prettifier: Expr[Prettifier],
    pos: Expr[source.Position], clue: Expr[Any]
  )
  (implicit refl: Reflection): Expr[Assertion] = {

    import refl._
    import quoted.Toolbox.Default._

    val tree = condition.unseal

    val bool = parse(tree.underlyingArgument.seal[Boolean], prettifier)
    '{ (~helper)(~bool, ~clue, ~pos) }
  }

  private def parse(condition: Expr[Boolean], prettifier: Expr[Prettifier])(implicit refl: Reflection): Expr[Bool] = {
    import refl._
    import quoted.Toolbox.Default._

    def exprStr: String = condition.show
    def defaultCase = '(Bool.simpleMacroBool(~condition, ~exprStr.toExpr, ~prettifier))

    // AssertionsSpec.this.convertToEqualizer[scala.Int](a).===(5)(scalactic.Equality.default[scala.Int])
    object TripleEqual {
      def isEqualizer(tp: Type): Boolean = true // tp <:< typeOf[TripleEqualsSupport#Equalizer[_]]

      def unapply(tree: Term): Option[(Term, Term, String, Term, Option[Term])] = tree match {
        case Term.Apply(Term.Select(Term.Apply(fun, lhs :: Nil), op), rhs :: Nil) if isEqualizer(fun.tpe) =>
          Some((fun, lhs, op, rhs, None))
        case Term.Apply(Term.Apply(Term.Select(Term.Apply(fun, lhs :: Nil), op), rhs :: Nil), equality :: Nil) if isEqualizer(fun.tpe)  =>
          Some((fun, lhs, op, rhs, Some(equality)))
        case _ => None
      }
    }

    condition.unseal match {
      case Term.Apply(Term.Select(lhs, op), rhs :: Nil) =>
        op match {
          case "==" =>
            val left = lhs.seal[Any]
            val right = rhs.seal[Any]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left == _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case "!=" =>
            val left = lhs.seal[Any]
            val right = rhs.seal[Any]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left != _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case ">" =>
            // blocked by tasty constructors
            // https://github.com/lampepfl/dotty/pull/5438
            val left = lhs.seal[Int]
            val right = rhs.seal[Int]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left > _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case "<" =>
            // blocked by tasty constructors
            // https://github.com/lampepfl/dotty/pull/5438
            val left = lhs.seal[Int]
            val right = rhs.seal[Int]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left < _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case ">=" =>
            // blocked by tasty constructors
            // https://github.com/lampepfl/dotty/pull/5438
            val left = lhs.seal[Int]
            val right = rhs.seal[Int]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left >= _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case "<=" =>
            // blocked by tasty constructors
            // https://github.com/lampepfl/dotty/pull/5438
            val left = lhs.seal[Int]
            val right = rhs.seal[Int]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left <= _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case "eq" =>
            val left = lhs.seal[AnyRef]
            val right = rhs.seal[AnyRef]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left `eq` _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case "ne" =>
            val left = lhs.seal[AnyRef]
            val right = rhs.seal[AnyRef]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left `ne` _right
              Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
            }
          case "||" =>
            val left = parse(lhs.seal[Boolean], prettifier)
            val right = parse(rhs.seal[Boolean], prettifier)
            '(~left || ~right)
          case "&&" =>
            val left = parse(lhs.seal[Boolean], prettifier)
            val right = parse(rhs.seal[Boolean], prettifier)
            '(~left && ~right)
          case _ =>
            defaultCase
        }
      // case TripleEqual(fn, lhs, op, rhs, Some(eq)) =>
      //   val fun = fn.seal[Any => TripleEqualsSupport#Equalizer[_]]
      //   val left = lhs.seal[Any]
      //   val right = rhs.seal[Any]
      //   val equality = eq.seal[Equality[Any]]
      //   op match {
      //     case "===" =>
      //       '{
      //         val _left   = ~left
      //         val _right  = ~right
      //         val _result = (~fun)(_left).===(_right)(~equality)
      //         Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
      //       }
      //     case "!==" =>
      //       '{
      //         val _left   = ~left
      //         val _right  = ~right
      //         val _result = (~fun)(_left).!==(_right)(~equality)
      //         Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
      //       }
      //   }
      // case TripleEqual(fn, lhs, op, rhs, None) =>
      //   val fun = fn.seal[Any => TripleEqualsSupport#Equalizer[_]]
      //   val left = lhs.seal[Any]
      //   val right = rhs.seal[Any]

      //   op match {
      //     case "===" =>
      //       '{
      //         val _left   = ~left
      //         val _right  = ~right
      //         val _result = (~fun)(_left) === _right
      //         Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
      //       }
      //     case "!==" =>
      //       '{
      //         val _left   = ~left
      //         val _right  = ~right
      //         val _result = (~fun)(_left) !== _right
      //         Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
      //       }
      //   }
      case Term.Select(left, "unary_!") =>
        val receiver = parse(left.seal[Boolean], prettifier)
        '{ !(~receiver) }
      case Term.Literal(_) =>
        '(Bool.simpleMacroBool(~condition, "", ~prettifier))
      case _ =>
        defaultCase
    }
  }
}