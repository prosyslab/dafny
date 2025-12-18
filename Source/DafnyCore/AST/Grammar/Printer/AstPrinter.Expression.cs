//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Text.Json.Nodes;
using DafnyCore;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public partial class AstPrinter {

    public JsonObject PrintMatchCaseArgument(MatchCase mc) {
      throw new NotImplementedException("AstPrinter.Expression: text printing is disabled in this AST printer.");
    }

    public JsonObject PrintExpression(Expression expr) {
      throw new NotImplementedException("AstPrinter.Expression: text printing is disabled in this AST printer.");
    }

    private JsonArray PrintFrameExpressionList(List<FrameExpression> fexprs) {
      throw new NotImplementedException("AstPrinter.Expression: text printing is disabled in this AST printer.");
    }
  }
}


