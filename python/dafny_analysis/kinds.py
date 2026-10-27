"""Lightweight Dafny declaration kind values shared by datatype models."""

from enum import StrEnum


class DefinitionKind(StrEnum):
    """Public Dafny declaration categories accepted on JSON boundaries."""

    CONSTANT = "constant"
    FUNCTION = "function"
    PREDICATE = "predicate"
    METHOD = "method"
    CONSTRUCTOR = "constructor"
    FUNCTION_BY_METHOD = "function-by-method"
    TWOSTATE_FUNCTION = "twostate function"
    TWOSTATE_PREDICATE = "twostate predicate"
    DATATYPE = "datatype"
    TYPE_SYNONYM = "type synonym"
    SUBSET_TYPE = "subset type"
    NEWTYPE = "newtype"
    ABSTRACT_TYPE = "abstract type"
    CLASS = "class"
    TRAIT = "trait"
    ITERATOR = "iterator"
    FIELD = "field"
    EXPORT = "export"
    LEAST_PREDICATE = "least predicate"
    GREATEST_PREDICATE = "greatest predicate"
