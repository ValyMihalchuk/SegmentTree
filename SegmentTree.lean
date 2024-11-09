-- This module serves as the root of the `SegmentTree` library.
-- Import modules here that should be built as part of the library.


import Aesop
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith




set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Parser
open Lean.Parser.Term
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax
