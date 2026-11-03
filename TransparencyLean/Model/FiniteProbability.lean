import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite probability with real-valued weights

The mathematical core uses finite sums and arbitrary real probabilities.
No rationality or positive-support assumption is made.
-/

namespace TransparencyLean

open scoped BigOperators

structure FiniteDist (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  sum_eq_one : ∑ ω, prob ω = 1

namespace FiniteDist

variable {Ω : Type*} [Fintype Ω]

@[ext] theorem ext (p q : FiniteDist Ω) (h : ∀ ω, p.prob ω = q.prob ω) : p = q := by
  cases p
  cases q
  congr
  exact funext h

def expect (p : FiniteDist Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, p.prob ω * f ω

@[simp] theorem expect_const (p : FiniteDist Ω) (r : ℝ) :
    p.expect (fun _ => r) = r := by
  simp [expect, ← Finset.sum_mul, p.sum_eq_one]

theorem expect_add (p : FiniteDist Ω) (f g : Ω → ℝ) :
    p.expect (fun ω => f ω + g ω) = p.expect f + p.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (p : FiniteDist Ω) (f g : Ω → ℝ) :
    p.expect (fun ω => f ω - g ω) = p.expect f - p.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (p : FiniteDist Ω) (r : ℝ) (f : Ω → ℝ) :
    p.expect (fun ω => r * f ω) = r * p.expect f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_mono (p : FiniteDist Ω) {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : p.expect f ≤ p.expect g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))

theorem expect_nonneg (p : FiniteDist Ω) {f : Ω → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ p.expect f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) (h ω))

theorem expect_finset_sum {I : Type*} (p : FiniteDist Ω) (S : Finset I)
    (f : I → Ω → ℝ) :
    p.expect (fun ω => ∑ i ∈ S, f i ω) = ∑ i ∈ S, p.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

def pointMass [DecidableEq Ω] (ω : Ω) : FiniteDist Ω where
  prob η := if η = ω then 1 else 0
  nonneg η := by split_ifs <;> norm_num
  sum_eq_one := by simp

@[simp] theorem expect_pointMass [DecidableEq Ω] (ω : Ω) (f : Ω → ℝ) :
    (pointMass ω).expect f = f ω := by
  simp [expect, pointMass]

end FiniteDist

end TransparencyLean
