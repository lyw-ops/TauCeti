/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Basic.Real.Pointwise

/-!
# Conversions used in the extended-valued maximal inequality.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- `ENNReal.ofReal` absorbs the positive part since it already vanishes on `(-∞, 0]`. -/
@[simp]
theorem ofReal_posPart (x : ℝ) : ENNReal.ofReal (x⁺) = ENNReal.ofReal x := by
  rcases le_total 0 x with hx | hx
  · rw [posPart_eq_self.2 hx]
  · rw [posPart_eq_zero.2 hx, ofReal_zero, ofReal_eq_zero.2 hx]

/-- For `1 < p`, `ENNReal.ofReal` commutes with the Hölder conjugate ratio `p / (p - 1)`. -/
theorem ofReal_div_sub_one {p : ℝ} (hp : 1 < p) :
    ENNReal.ofReal (p / (p - 1)) = ENNReal.ofReal p / (ENNReal.ofReal p - 1) := by
  rw [ofReal_div_of_pos (sub_pos.2 hp), ofReal_sub _ zero_le_one, ofReal_one]

end ENNReal

namespace TauCeti

variable {α β : Type*}

end TauCeti
