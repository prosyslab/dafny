// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using Xunit;

// Run test collections sequentially so campaigns do not compete for fixed deadlines.
[assembly: CollectionBehavior(DisableTestParallelization = true)]
