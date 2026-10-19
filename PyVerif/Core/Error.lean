import Std

namespace PyVerif

/-- Observable language failures, kept distinct from running out of fuel. -/
inductive Error where
  | divisionByZero
  | overflow
  | indexOutOfBounds
  | assertionFailure
  deriving Repr, DecidableEq, Inhabited

/-- A malformed source/IR access is stuck; an arithmetic exception is failed. -/
inductive Fault where
  | failed : Error → Fault
  | stuck
  deriving Repr, DecidableEq, Inhabited

abbrev Eval (α : Type) := Except Fault α

end PyVerif
