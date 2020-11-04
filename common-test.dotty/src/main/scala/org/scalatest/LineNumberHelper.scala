package org.scalatest

import scala.quoted._

private[scalatest] trait LineNumberHelper {
  inline def thisLineNumber = ${ LineNumberMacro.thisLineNumberImpl }
}

object LineNumberMacro {
  def thisLineNumberImpl(implicit qctx: QuoteContext): Expr[Int] =
    Expr(qctx.reflect.Position.ofMacroExpansion.startLine)
}
