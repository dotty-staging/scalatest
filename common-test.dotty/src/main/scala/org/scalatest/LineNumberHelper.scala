package org.scalatest

import scala.quoted._

private[scalatest] trait LineNumberHelper {
  inline def thisLineNumber = ${ LineNumberMacro.thisLineNumberImpl }
}

object LineNumberMacro {
  def thisLineNumberImpl(implicit qctx: QuoteContext): Expr[Int] = {
    import qctx.reflect._
    Expr(rootPosition.startLine)
  }
}
