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
  def assert(condition: Expr[Boolean], prettifier: Expr[Prettifier], pos: Expr[source.Position], clue: Expr[Any])(implicit refl: Reflection): Expr[Assertion] = {
    import refl._
    import quoted.Toolbox.Default._

    val tree = condition.unseal
    def exprStr: String = condition.show

    tree.underlyingArgument match {
      case Term.Apply(Term.Select(lhs, op), rhs :: Nil) =>
        op match {
          case "==" =>
            val left = lhs.seal[Any]
            val right = rhs.seal[Any]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left == _right
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
            }
          case "!=" =>
            val left = lhs.seal[Any]
            val right = rhs.seal[Any]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left != _right
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
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
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
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
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
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
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
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
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
            }
          case "===" =>
            val left = lhs.seal[TripleEqualsSupport#Equalizer[_]]
            val right = rhs.seal[Any]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left === _right
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
            }
          case "eq" =>
            val left = lhs.seal[AnyRef]
            val right = rhs.seal[AnyRef]
            '{
              val _left   = ~left
              val _right  = ~right
              val _result = _left `eq` _right
              val _bool = Bool.binaryMacroBool(_left, ~op.toExpr, _right, _result, ~prettifier)
              Assertions.assertionsHelper.macroAssert(_bool, ~clue, ~pos)
            }
          case _ =>
            '(Assertions.assertionsHelper.macroAssert(Bool.simpleMacroBool(~condition, ~exprStr.toExpr, ~prettifier), ~clue, ~pos))
        }
      case Term.Select(left, "unary_!") =>
        '(Assertions.assertionsHelper.macroAssert(Bool.simpleMacroBool(~condition, ~exprStr.toExpr, ~prettifier), ~clue, ~pos))
      case Term.Literal(_) =>
        '(Assertions.assertionsHelper.macroAssert(Bool.simpleMacroBool(~condition, "", ~prettifier), ~clue, ~pos))
      case _ =>
        '(Assertions.assertionsHelper.macroAssert(Bool.simpleMacroBool(~condition, ~exprStr.toExpr, ~prettifier), ~clue, ~pos))
    }

  }

//   /**
//    * Provides implementation for <code>Assertions.assume(booleanExpr: Boolean)</code>, with rich error message.
//    *
//    * @param context macro context
//    * @param condition original condition expression
//    * @return transformed expression that performs the assumption check and throw <code>TestCanceledException</code> with rich error message if assumption failed
//    */
//   def assume(context: Context)(condition: context.Expr[Boolean])(prettifier: context.Expr[Prettifier], pos: context.Expr[source.Position]): context.Expr[Assertion] = {
//     import context.universe._
//     new BooleanMacro[context.type](context).genMacro[Assertion](
//       Select(
//         Select(
//           Select(
//             Select(
//               Ident(newTermName("_root_")),
//               newTermName("org")
//             ),
//             newTermName("scalatest")
//           ),
//           newTermName("Assertions")
//         ),
//         newTermName("assertionsHelper")
//       ),
//       condition,
//       "macroAssume",
//       context.literal(""),
//       prettifier,
//       pos)
//   }

//   /**
//    * Provides implementation for <code>Assertions.assume(booleanExpr: Boolean, clue: Any)</code>, with rich error message.
//    *
//    * @param context macro context
//    * @param condition original condition expression
//    * @param clue original clue expression
//    * @return transformed expression that performs the assumption check and throw <code>TestCanceledException</code> with rich error message (clue included) if assumption failed
//    */
//   def assumeWithClue(context: Context)(condition: context.Expr[Boolean], clue: context.Expr[Any])(prettifier: context.Expr[Prettifier], pos: context.Expr[source.Position]): context.Expr[Assertion] = {
//     import context.universe._
//     new BooleanMacro[context.type](context).genMacro[Assertion](
//       Select(
//         Select(
//           Select(
//             Select(
//               Ident(newTermName("_root_")),
//               newTermName("org")
//             ),
//             newTermName("scalatest")
//           ),
//           newTermName("Assertions")
//         ),
//         newTermName("assertionsHelper")
//       ),
//       condition,
//       "macroAssume",
//       clue,
//       prettifier,
//       pos)
//   }
}