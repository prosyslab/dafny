//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Diagnostics.Contracts;
using System.Text.Json.Nodes;

namespace Microsoft.Dafny {

  public partial class AstPrinter {
    /// <summary>
    /// This printer emits JSON. Signatures intentionally do not expose formatting parameters (indent, semicolons, ...).
    /// </summary>
    public JsonObject PrintStatement(Statement stmt) {
      Contract.Requires(stmt != null);
      throw new NotImplementedException("AstPrinter.Statement: JSON printing for statements is not implemented yet.");
    }

    public JsonObject PrintConcreteUpdateStatement(ConcreteAssignStatement stmt) {
      Contract.Requires(stmt != null);
      throw new NotImplementedException("AstPrinter.Statement: JSON printing for statements is not implemented yet.");
    }

    public JsonObject PrintBlockStmt(BlockStmt stmt) {
      Contract.Requires(stmt != null);
      throw new NotImplementedException("AstPrinter.Statement: JSON printing for statements is not implemented yet.");
    }

    public JsonObject PrintPredicateStmt(Statement stmt) {
      Contract.Requires(stmt != null);
      throw new NotImplementedException("AstPrinter.Statement: JSON printing for statements is not implemented yet.");
    }
  }
}

