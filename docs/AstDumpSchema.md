---
title: AST Dump JSON Schema
---

# AST Dump JSON Schema

The `ast-dump` command writes a compact JSON representation of Dafny's resolved AST.

```text
dafny ast-dump --output out.ast.json input.dfy
```

This document describes the current output schema for `version: 4`.

## Top-level object

The output file is a single JSON object with these fields:

- `format`: always `"dafny-resolved-ast"`
- `version`: schema version, currently `4`
- `resolved`: always `true`
- `programName`: input program name
- `root`: root AST node

Example:

```json
{
  "format": "dafny-resolved-ast",
  "version": 4,
  "resolved": true,
  "programName": "even.dfy",
  "root": {
    "kind": "program",
    "name": "even.dfy",
    "modules": [ ... ]
  }
}
```

## Common node shape

Every AST node contains at least:

- `kind`: node kind discriminator

Some nodes also contain:

- `name`: declaration or identifier name
- `value`: literal value
- `type`: a recursive type object
- `typeSource`: optional, currently used when a local variable type was inferred
- `location`: source location for modules, classes, functions, and methods

Location objects have this shape:

```json
{
  "file": "even.dfy",
  "line": 1,
  "column": 1
}
```

Line and column numbers are 1-based.

## Type object schema

All type-bearing positions use the same field name: `type`.

Primitive types:

```json
{ "kind": "int" }
{ "kind": "bool" }
{ "kind": "char" }
{ "kind": "real" }
{ "kind": "fp64" }
{ "kind": "big_ordinal" }
```

Bitvectors:

```json
{ "kind": "bitvector", "width": 32 }
```

Collections:

```json
{ "kind": "seq", "element": { "kind": "int" } }
{ "kind": "set", "element": { "kind": "int" } }
{ "kind": "iset", "element": { "kind": "int" } }
{ "kind": "multiset", "element": { "kind": "int" } }
```

Maps:

```json
{
  "kind": "map",
  "key": { "kind": "int" },
  "value": {
    "kind": "iset",
    "element": { "kind": "int" }
  }
}
```

Named and generic types:

```json
{ "kind": "named", "name": "C" }
{ "kind": "named", "name": "Box", "args": [ { "kind": "int" } ] }
{ "kind": "named", "name": "Node", "nullable": true }
```

Type parameters:

```json
{ "kind": "type_parameter", "name": "T" }
```

Arrow types:

```json
{
  "kind": "arrow",
  "parameters": [ { "kind": "int" }, { "kind": "bool" } ],
  "result": { "kind": "bool" },
  "arrowKind": "partial"
}
```

Proxy types:

```json
{ "kind": "proxy" }
```

## Node-specific schemas

The serializer prefers node-specific fields over generic child arrays.

### Program

```json
{
  "kind": "program",
  "name": "even.dfy",
  "modules": [ ModuleNode, ... ]
}
```

### Module

```json
{
  "kind": "module",
  "location": { "file": "even.dfy", "line": 1, "column": 1 },
  "name": "A",
  "members": [ FunctionNode | MethodNode | ClassNode | ... ],
  "declarations": [ ClassNode | ModuleNode | ... ]
}
```

- `members` is used for declarations in the default module body.
- `declarations` is used for non-default nested declarations.

### Class and other top-level declarations with members

```json
{
  "kind": "class",
  "location": { "file": "even.dfy", "line": 1, "column": 10 },
  "name": "C",
  "typeParameters": [ "T" ],
  "traits": [ TypeObject, ... ],
  "members": [ ... ]
}
```

The exact `kind` depends on the Dafny declaration kind, for example `class`, `trait`, or `datatype`.

### Function

```json
{
  "kind": "function",
  "location": { "file": "even.dfy", "line": 1, "column": 10 },
  "name": "is_even",
  "typeParameters": [ ... ],
  "parameters": [ ParameterNode, ... ],
  "type": { "kind": "bool" },
  "requires": [ ExpressionNode, ... ],
  "ensures": [ ExpressionNode, ... ],
  "reads": [ ExpressionNode, ... ],
  "decreases": [ ExpressionNode, ... ],
  "body": ExpressionNode,
  "byMethodBody": BlockNode
}
```

`body` and `byMethodBody` are optional. A function normally has `body`; a function-by-method may also have `byMethodBody`.

### Method

```json
{
  "kind": "method",
  "location": { "file": "even.dfy", "line": 7, "column": 1 },
  "name": "IsEven",
  "typeParameters": [ ... ],
  "parameters": [ ParameterNode, ... ],
  "returns": [ ReturnParameterNode, ... ],
  "requires": [ ExpressionNode, ... ],
  "ensures": [ ExpressionNode, ... ],
  "reads": [ ExpressionNode, ... ],
  "modifies": [ ExpressionNode, ... ],
  "decreases": [ ExpressionNode, ... ],
  "body": BlockNode
}
```

Methods do not synthesize a single return type. Each return parameter carries its own `type`.

### Parameters

Input parameter:

```json
{
  "kind": "parameter",
  "name": "x",
  "parameterKind": "in",
  "type": { "kind": "int" },
  "defaultValue": ExpressionNode
}
```

Return parameter:

```json
{
  "kind": "return_parameter",
  "name": "y",
  "parameterKind": "out",
  "type": { "kind": "bool" }
}
```

### Block

```json
{
  "kind": "block",
  "statements": [ StatementNode, ... ]
}
```

### Variable declaration

```json
{
  "kind": "var_decl",
  "locals": [ LocalVariableNode, ... ],
  "initializer": AssignNode
}
```

Local variable:

```json
{
  "kind": "local_variable",
  "name": "result",
  "type": { "kind": "bool" }
}
```

If the type was inferred rather than explicitly written, the node may also contain:

```json
{ "typeSource": "inferred" }
```

### Assignment

```json
{
  "kind": "assign",
  "lhs": ExpressionNode,
  "rhs": ExpressionNode
}
```

For multi-assignment or unresolved forms, the serializer may instead emit arrays:

```json
{
  "kind": "assign",
  "lhs": [ ExpressionNode, ... ],
  "rhs": [ ExpressionNode, ... ]
}
```

### If statement

```json
{
  "kind": "if",
  "condition": ExpressionNode,
  "then": StatementNode,
  "else": StatementNode
}
```

### Assert statement

```json
{
  "kind": "assert",
  "condition": ExpressionNode
}
```

### Call

Method call:

```json
{
  "kind": "call",
  "method": "IsEven",
  "receiver": ExpressionNode,
  "arguments": [ ExpressionNode, ... ],
  "results": [ ExpressionNode, ... ]
}
```

Function call expression:

```json
{
  "kind": "call",
  "name": "is_even",
  "receiver": ExpressionNode,
  "arguments": [ ExpressionNode, ... ],
  "type": { "kind": "bool" }
}
```

### Binary expression

```json
{
  "kind": "binary",
  "operator": "==",
  "left": ExpressionNode,
  "right": ExpressionNode,
  "type": { "kind": "bool" }
}
```

### Member access

```json
{
  "kind": "member_access",
  "member": "fieldOrMethodName",
  "receiver": ExpressionNode,
  "type": TypeObject
}
```

### Identifier and name-like expressions

```json
{
  "kind": "identifier",
  "name": "x",
  "type": { "kind": "int" }
}
```

```json
{
  "kind": "name",
  "name": "result",
  "type": { "kind": "bool" }
}
```

### Literals

Examples:

```json
{ "kind": "literal.int", "value": "3", "type": { "kind": "int" } }
{ "kind": "literal.bool", "value": true, "type": { "kind": "bool" } }
{ "kind": "literal.string", "value": "hello" }
{ "kind": "literal.null" }
```

### Negation

```json
{
  "kind": "negation",
  "operator": "-",
  "operand": ExpressionNode,
  "type": { "kind": "int" }
}
```

### Set and iset display

```json
{
  "kind": "set",
  "elements": [ ExpressionNode, ... ],
  "type": {
    "kind": "set",
    "element": { "kind": "int" }
  }
}
```

```json
{
  "kind": "iset",
  "elements": [ ExpressionNode, ... ],
  "type": {
    "kind": "iset",
    "element": { "kind": "int" }
  }
}
```

### Specification clauses

```json
{
  "kind": "specification",
  "expressions": [ ExpressionNode, ... ]
}
```

## Design rules

The AST dump intentionally omits high-noise metadata:

- no `source`
- no `snippet`
- no old string type fields like `resolvedType`, `declaredType`, `returnType`, or `resolvedVariableType`
- no graph-level `nodes`, `symbols`, or `references`

The schema favors:

- compact resolved AST output
- node-specific field names
- one canonical recursive `type` field
- human-readable structure for tools and analysis pipelines

## Compatibility notes

- `version: 1` is the current compact schema with unified recursive type objects.
- New node kinds may be added over time.
- Rare node kinds may still use a small fallback shape with `kind` and `children` if they have not yet been specialized.
