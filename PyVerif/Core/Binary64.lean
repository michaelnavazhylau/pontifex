import Std

namespace PyVerif

/-- Two-tier binary64 boundary value.

    `bits` is authoritative for wire transport, identity, and sign operations,
    preserving signed zeros, subnormals, infinities, and raw NaN payloads.
    `value` is Lean's built-in `Float` used by arithmetic and comparisons.

    The two tiers are related by construction: `ofBits` sets `value` with
    `Float.ofBits`, `ofFloat` stores the Float's bits.  The correspondence
    between native `Float` operations and IEEE-754 is a documented, tested trust
    boundary, not a kernel theorem. -/
structure Binary64 where
  bits : UInt64
  value : Float
  deriving Repr, Inhabited

namespace Binary64

def ofBits (bits : UInt64) : Binary64 := ⟨bits, Float.ofBits bits⟩

def ofFloat (x : Float) : Binary64 := ⟨x.toBits, x⟩

def toBits (x : Binary64) : UInt64 := x.bits

def toFloat (x : Binary64) : Float := x.value

theorem ofBits_bits (bits : UInt64) : (ofBits bits).bits = bits := rfl

theorem ofBits_value (bits : UInt64) : (ofBits bits).toFloat = Float.ofBits bits := rfl

theorem ofFloat_bits (x : Float) : (ofFloat x).bits = x.toBits := rfl

theorem ofFloat_value (x : Float) : (ofFloat x).toFloat = x := rfl

/-- Raw representation round-trip; independent of floating-point computation. -/
theorem bits_roundtrip (bits : UInt64) : (ofBits bits).toBits = bits := rfl

def signBit : UInt64 := 0x8000000000000000

def magnitudeMask : UInt64 := 0x7fffffffffffffff

/-- Flip the sign bit and negate the value tier. -/
def neg (x : Binary64) : Binary64 := ⟨x.bits ^^^ signBit, -x.value⟩

/-- Clear the sign bit and take the value's absolute value. -/
def abs (x : Binary64) : Binary64 := ⟨x.bits &&& magnitudeMask, Float.abs x.value⟩

theorem neg_bits (x : Binary64) : (neg x).bits = x.bits ^^^ signBit := rfl

theorem neg_value (x : Binary64) : (neg x).toFloat = -x.toFloat := rfl

theorem abs_bits (x : Binary64) : (abs x).bits = x.bits &&& magnitudeMask := rfl

theorem abs_value (x : Binary64) : (abs x).toFloat = Float.abs x.toFloat := rfl

end Binary64
end PyVerif
