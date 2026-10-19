import Std

namespace PyVerif

/-- Bit-authoritative binary64 boundary values. Lean's built-in Float model
    canonicalizes NaNs; retaining raw UInt64 avoids losing payloads/signaling
    bits during identity transport or literal loading. Arithmetic explicitly
    passes through the built-in Float model and may canonicalize computed NaNs. -/
structure Binary64 where
  bits : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace Binary64

def ofBits (bits : UInt64) : Binary64 := ⟨bits⟩
def toBits (x : Binary64) : UInt64 := x.bits
def toFloat (x : Binary64) : Float := Float.ofBits x.bits
def ofFloat (x : Float) : Binary64 := ⟨x.toBits⟩

/-- Pure bit transport, independent of floating-point computation or compiler
    reduction axioms. This includes every NaN payload and both zero signs. -/
theorem bits_roundtrip (bits : UInt64) : (ofBits bits).toBits = bits := rfl

/-- Unary negation is a sign-bit flip, including signed zeros and NaNs. -/
def neg (x : Binary64) : Binary64 := ⟨x.bits ^^^ 0x8000000000000000⟩

def abs (x : Binary64) : Binary64 := ⟨x.bits &&& 0x7fffffffffffffff⟩

end Binary64
end PyVerif
