/-
All the proofs are taken from the miniF2F github and translated into Lean 4:
https://github.com/openai/miniF2F/blob/main/lean/src/valid.lean
-/

import Aesop
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators
open Real
open Nat
open Topology

theorem mathd_algebra_182 (y : ℂ) :
  7 * (3 * y + 2) = 21 * y + 14 :=
by ring_nf

theorem mathd_algebra_116
  (k x: ℝ)
  (h₀ : x = (13 - Real.sqrt 131) / 4)
  (h₁ : 2 * x^2 - 13 * x + k = 0) :
  k = 19/4 := by
  rw [h₀] at h₁
  rw [eq_comm.mp (add_eq_zero_iff_neg_eq.mp h₁)]
  norm_num
  rw [pow_two]
  rw [mul_sub]
  rw [sub_mul, sub_mul]
  rw [Real.mul_self_sqrt _]
  ring
  linarith

theorem mathd_algebra_462 :
  ((1 : ℚ)/ 2 + 1 / 3) * (1 / 2 - 1 / 3) = 5 / 36 :=
by norm_num

theorem amc12_2001_p9
  (f : ℝ → ℝ)
  (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x / y)
  (h₁ : f 500 = 3) : f 600 = 5 / 2 := by
  specialize h₀ 500 (by norm_num) (6 / 5) (by norm_num)
  have h2 : f 600 = f (500 * (6 / 5)) := by norm_num
  rw [h2, h₀, h₁]
  norm_num

theorem mathd_numbertheory_48
  (b : ℕ)
  (h₀ : 0 < b)
  (h₁ : 3 * b^2 + 2 * b + 1 = 57) :
  b = 4 := by
  nlinarith

theorem mathd_algebra_48
  (q e : ℂ)
  (h₀ : q = 9 - 4 * Complex.I)
  (h₁ : e = -3 - 4 * Complex.I) : q - e = 12 := by
  rw [h₀, h₁]
  ring

theorem mathd_numbertheory_132 :
  2004 % 12 = 0 := by
  norm_num

theorem mathd_numbertheory_188 :
  Nat.gcd 180 168 = 12 := by
  have step1 : Nat.gcd 180 168 = Nat.gcd (180 % 168) 168 := Nat.gcd_rec 180 168
  have step2 : 180 % 168 = 12 := by norm_num
  rw [step2] at step1
  have step3 : Nat.gcd 12 168 = Nat.gcd 12 (168 % 12) := Nat.gcd_rec 12 168
  have step4 : 168 % 12 = 0 := by norm_num
  rw [step4] at step3
  have step5 : Nat.gcd 12 0 = 12 := Nat.gcd_zero_right 12
  rw [step5] at step3
  exact step3

theorem mathd_algebra_422
  (x : ℝ)
  (σ : Equiv ℝ ℝ)
  (h₀ : ∀ x, σ.1 x = 5 * x - 12)
  (h₁ : σ.1 (x + 1) = σ.2 x) :
  x = 47 / 24 := by
  field_simp [h₀, mul_add, add_mul, sub_add_cancel, mul_assoc, add_comm]
  have := congr_arg σ.toFun h₁
  rw [h₀] at this
  rw [h₀] at this
  symm
  norm_num at this
  linarith

theorem mathd_numbertheory_109
  (v : ℕ → ℕ)
  (h₀ : ∀ n, v n = 2 * n - 1) :
  (∑ k in Finset.range 101, v k) % 7 = 4 :=
by
  norm_num
  simp [h₀]
  have h₁ : Finset.range 101 = Finset.Ico 0 101 := rfl
  rw [h₁]
  norm_num [Finset.sum_Ico_succ_top]
  simp_all only [Ico_zero_eq_range]
  apply
    Eq.refl


theorem mathd_numbertheory_24 :
  (∑ k in (Finset.Icc 1 9), 11^k) % 100 = 59 := by
  apply
    Eq.refl

theorem mathd_algebra_101
  (x : ℝ)
  (h₀ : x^2 - 5 * x - 4 ≤ 10) :
  x ≥ -2 ∧ x ≤ 7 :=
by
  apply And.intro
  all_goals nlinarith

theorem amc12_2000_p5
  (x p : ℝ)
  (h₀ : x < 2)
  (h₁ : abs (x - 2) = p) :
  x - p = 2 - 2 * p := by
  suffices  abs (x - 2) = -(x - 2) by
    rw [h₁] at this
    linarith
  apply abs_of_neg
  linarith

theorem mathd_numbertheory_200 :
  139 % 11 = 7 := by
norm_num

theorem mathd_algebra_140
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : ∀ x, 24 * x^2 - 19 * x - 35 = (((a * x) - 5) * ((2 * (b * x)) + c))) :
  a * b - 3 * c = -9 := by
  have h₂ := h₁ 0
  have h₂ := h₁ 1
  have h₃ := h₁ (-1)
  linarith

theorem mathd_algebra_455
  (x : ℝ)
  (h₀ : 2 * (2 * (2 * (2 * x))) = 48) :
  x = 3 := by
  linarith

theorem mathd_numbertheory_45 :
  (Nat.gcd 6432 132) + 11 = 23 := by
  simp only [Nat.gcd_comm]
  norm_num

theorem mathd_numbertheory_739 :
  9! % 10 = 0 := by
  norm_num
  apply
    Eq.refl

theorem mathd_algebra_245
  (x : ℝ)
  (h₀ : x ≠ 0) :
  (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by
  field_simp [(show x ≠ 0 by simpa using h₀), mul_comm x]
  ring

theorem mathd_algebra_126
  (x y : ℝ)
  (h₀ : 2 * 3 = x - 9)
  (h₁ : 2 * (-5) = y + 1) :
  x = 15 ∧ y = -11 := by
  have hx : x = 15 := by linarith [h₀]
  have hy : y = -11 := by linarith [h₁]
  exact ⟨hx, hy⟩

  theorem amc12a_2008_p2
  (x : ℝ)
  (h₀ : x * (1 / 2 + 2 / 3) = 1) :
  x = 6 / 7 := by
  linarith

  theorem mathd_algebra_35
  (p q : ℝ → ℝ)
  (h₀ : ∀ x, p x = 2 - x^2)
  (h₁ : ∀ x ≠ 0, q x = 6 / x) :
  p (q 2) = -7 := by
  rw [h₀, h₁]
  ring
  linarith

theorem amc12a_2021_p7
  (x y : ℝ) :
  1 ≤ ((x * y) - 1)^2 + (x + y)^2 := by
  ring_nf
  nlinarith

theorem mathd_algebra_327
  (a : ℝ)
  (h₀ : 1 / 5 * abs (9 + 2 * a) < 1) :
  -7 < a ∧ a < -2 :=
by
  have h₂ : abs (9 + 2 * a) < 5 := by linarith
  have h₃ := abs_lt.mp h₂
  obtain ⟨h₃_left, h₃_right⟩ := h₃
  apply And.intro
  { nlinarith [h₃_left] }
  { nlinarith [h₃_right] }

theorem aime_1984_p15
  (x y z w : ℝ)
  (h₀ : (x^2 / (2^2 - 1)) + (y^2 / (2^2 - 3^2)) + (z^2 / (2^2 - 5^2)) + (w^2 / (2^2 - 7^2)) = 1)
  (h₁ : (x^2 / (4^2 - 1)) + (y^2 / (4^2 - 3^2)) + (z^2 / (4^2 - 5^2)) + (w^2 / (4^2 - 7^2)) = 1)
  (h₂ : (x^2 / (6^2 - 1)) + (y^2 / (6^2 - 3^2)) + (z^2 / (6^2 - 5^2)) + (w^2 / (6^2 - 7^2)) = 1)
  (h₃ : (x^2 / (8^2 - 1)) + (y^2 / (8^2 - 3^2)) + (z^2 / (8^2 - 5^2)) + (w^2 / (8^2 - 7^2)) = 1) :
  x^2 + y^2 + z^2 + w^2 = 36 := by
  revert x y z w h₀ h₁ h₂ h₃
  ring_nf
  intros x y z w h
  intros h
  intros
  linarith

theorem mathd_algebra_192
  (q e d : ℂ)
  (h₀ : q = 11 - (5 * Complex.I))
  (h₁ : e = 11 + (5 * Complex.I))
  (h₂ : d = 2 * Complex.I) :
  q * e * d = 292 * Complex.I := by
  rw [h₀, h₁, h₂]
  ring_nf
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, pow_two, Complex.I_mul_I]
    norm_num
  rw [hI3]
  ring

theorem amc12b_2002_p6
  (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : ∀ x, x^2 + a * x + b = (x - a) * (x - b)) :
  a = 1 ∧ b = -2 := by
  have h₂ := h₁ a
  have h₃ := h₁ b
  have h₄ := h₁ 0
  simp at *
  have h₅ : b * (1 - a) = 0 := by linarith
  simp at h₅
  cases' h₅ with h₅ h₆
  exfalso
  exact absurd h₅ h₀.2
  have h₆ : a = 1 := by linarith
  constructor
  exact h₆
  rw [h₆] at h₂
  linarith

theorem mathd_numbertheory_102 :
  (2^8) % 5 = 1 := by
  norm_num

theorem mathd_numbertheory_81 :
  71 % 3 = 2 := by
  norm_num

theorem mathd_algebra_110
  (q e : ℂ)
  (h₀ : q = 2 - 2 * Complex.I)
  (h₁ : e = 5 + 5 * Complex.I) :
  q * e = 20 := by

  rw [h₀, h₁]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring

theorem mathd_algebra_15
  (s : ℕ → ℕ → ℕ)
  (h₀ : ∀ a b, 0 < a ∧ 0 < b → s a b = a^(b:ℕ) + b^(a:ℕ)) :
  s 2 6 = 100 := by
  rw [h₀]
  rfl
  norm_num

theorem mathd_numbertheory_640 :
  (91145 + 91146 + 91147 + 91148) % 4 = 2 := by
  norm_num

theorem algebra_2rootsintpoly_am10tap11eqasqpam110
  (a : ℂ) :
  (a - 10) * (a + 11) = a^2 + a - 110 := by
  ring

theorem mathd_algebra_43
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x + b)
  (h₁ : f 7 = 4)
  (h₂ : f 6 = 3) :
  f 3 = 0 := by
  rw [h₀] at *
  linarith

theorem mathd_algebra_55
  (q p : ℝ)
  (h₀ : q = 2 - 4 + 6 - 8 + 10 - 12 + 14)
  (h₁ : p = 3 - 6 + 9 - 12 + 15 - 18 + 21) :
  q / p = 2 / 3 := by
  rw [h₀, h₁]
  ring

theorem algebra_sqineq_2at2pclta2c2p41pc
  (a c : ℝ) :
  2 * a * (2 + c) ≤ a^2 + c^2 + 4 * (1 + c) :=
by
  suffices  0 ≤ (c - a)^2 + 2^2 + 2 * 2 * (c - a) by nlinarith
  suffices  0 ≤ (c - a + 2)^2 by nlinarith
  exact pow_two_nonneg (c - a + 2)

theorem mathd_algebra_214
  (a : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * (x - 2)^2 + 3)
  (h₁ : f 4 = 4) :
  f 6 = 7 := by
  revert h₁
  simp [h₀]
  intro
  nlinarith

theorem mathd_algebra_96
  (x y z a : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : Real.log x - Real.log y = a)
  (h₂ : Real.log y - Real.log z = 15)
  (h₃ : Real.log z - Real.log x = -7) :
  a = -8 := by
  nlinarith [h₁, h₂, h₃]

theorem amc12_2001_p2
  (a b n : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9)
  (h₁ : 0 ≤ b ∧ b ≤ 9)
  (h₂ : n = 10 * a + b)
  (h₃ : n = a * b + a + b) :
  b = 9 := by
  rw [h₂] at h₃
  simp at h₃
  have h₄ : 10 * a = (b + 1) * a := by linarith
  simp at h₄
  cases' h₄ with h₅ h₆
  linarith
  exfalso
  simp [*, le_refl] at *

  theorem amc12a_2009_p2 :
  1 + (1 / (1 + (1 / (1 + 1)))) = (5 : ℚ) / 3 := by
  norm_num


theorem mathd_algebra_234
  (d : ℝ)
  (h₀ : 27 / 125 * d = 9 / 25) :
  3 / 5 * d^3 = 25 / 9 := by
  field_simp
  rw [mul_right_comm, pow_succ, mul_comm]
  { nlinarith }

theorem mathd_numbertheory_136
  (n : ℕ)
  (h₀ : 123 * n + 17 = 39500) : n = 321 :=
by
  linarith

theorem amc12_2000_p11
  (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : a * b = a - b) :
  a / b + b / a - a * b = 2 := by
  field_simp [h₀.1, h₀.2]
  simp only [h₁, mul_comm, mul_sub]
  ring

theorem amc12b_2003_p9
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x + b)
  (h₁ : f 6 - f 2 = 12) :
  f 12 - f 2 = 30 := by
  revert h₁
  simp only [h₀]
  intro
  linarith

theorem algebra_2complexrootspoly_xsqp49eqxp7itxpn7i
  (x : ℂ) :
  x^2 + 49 = (x + (7 * Complex.I)) * (x + (-7 * Complex.I)) := by
  ring_nf
  rw [pow_two, pow_two, Complex.I_mul_I]
  ring

theorem mathd_algebra_132
  (x : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 2)
  (h₁ : ∀ x, g x = x^2)
  (h₂ : f (g x) = g (f x)) :
  x = - 1/2 := by
  norm_num
  simp [*, -one_div] at *
  field_simp [h₁]
  linarith

theorem mathd_algebra_37
  (x y : ℝ)
  (h₀ : x + y = 7)
  (h₁ : 3 * x + y = 45) :
  x^2 - y^2 = 217 :=
by
  nlinarith

theorem algebra_sqineq_36azm9asqle36zsq
  (z a : ℝ) :
  36 * (a * z) - 9 * a^2 ≤ 36 * z^2 :=
by
  suffices  4 * (a * z) - a^2 ≤ 4 * z^2 by nlinarith
  suffices 0 ≤ (a - 2 * z)^2 by nlinarith
  exact pow_two_nonneg (a - 2 * z)

theorem mathd_algebra_104
  (x : ℝ)
  (h₀ : 125 / 8 = x / 12) :
  x = 375 / 2 :=
by
  linarith

theorem algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta
  (b c d a : ℂ) :
  (a - d) * (a - c) * (a - b) = -(((a^2 - (b + c) * a) + c * b) * d) + (a^2 - (b + c) * a + c * b) * a :=
by
  ring

theorem mathd_algebra_190 :
  ((3 : ℝ) / 8 + 7 / 8) / (4 / 5) = 25 / 16 :=
by
  norm_num

theorem mathd_numbertheory_101 :
  (17 * 18) % 4 = 2 :=
by
  norm_num

theorem algebra_sqineq_4bap1lt4bsqpap1sq
  (a b : ℝ) :
  4 * b * (a + 1) ≤ 4 * b^2 + (a + 1)^2 :=
by
  suffices 0 ≤ (2 * b - (a + 1))^2 by nlinarith
  exact pow_two_nonneg (2 * b - (a + 1))

theorem mathd_algebra_109
  (a b : ℝ)
  (h₀ : 3 * a + 2 * b = 12)
  (h₁ : a = 4) :
  b = 0 :=
by
  linarith

theorem algebra_2rootspoly_apatapbeq2asqp2ab
  (a b : ℂ) :
  (a + a) * (a + b) = 2 * a^2 + 2 * (a * b) := by
  ring

theorem mathd_algebra_568
  (a : ℝ) :
  (a - 1) * (a + 1) * (a + 2) - (a - 2) * (a + 1) = a^3 + a^2 := by
  linarith

theorem mathd_algebra_159
  (b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 3 * x^4 - 7 * x^3 + 2 * x^2 - b * x + 1)
  (h₁ : f 1 = 1) :
  b = -2 :=
by
  rw [h₀] at h₁
  linarith


theorem algebra_manipexpr_apbeq2cceqiacpbceqm2
  (a b c : ℂ)
  (h₀ : a + b = 2 * c)
  (h₁ : c = Complex.I) :
  a * c + b * c = -2 :=
by
  rw [← add_mul, h₀, h₁, mul_assoc, Complex.I_mul_I]
  ring

theorem mathd_algebra_67
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = 5 * x + 3)
  (h₁ : ∀ x, g x = x^2 - 2) :
  g (f (-1)) = 2 := by
  rw [h₀, h₁]
  ring

theorem mathd_algebra_123
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a + b = 20)
  (h₂ : a = 3 * b) :
  a - b = 10 :=
by
  rw [h₂] at h₁
  rw [h₂]
  have h₃ : b = 5 := by linarith
  rw [h₃]

theorem mathd_numbertheory_30 :
  (33818^2 + 33819^2 + 33820^2 + 33821^2 + 33822^2) % 17 = 0 := by
  simp_all only [reducePow,
    reduceAdd,
    reduceMod]

theorem mathd_numbertheory_961 :
  2003 % 11 = 1 :=
by
  norm_num

theorem algebra_manipexpr_2erprsqpesqeqnrpnesq
  (e r : ℂ) :
  2 * (e * r) + (e^2 + r^2) = (-r + (-e))^2 :=
by
  ring

theorem mathd_algebra_119
  (d e : ℝ)
  (h₀ : 2 * d = 17 * e - 8)
  (h₁ : 2 * e = d - 9) :
  e = 2 :=
by
  linarith

theorem numbertheory_2dvd4expn
  (n : ℕ)
  (h₀ : n ≠ 0) :
  2 ∣ 4^n :=
by
  revert n h₀
  intros k rfl
  norm_num
  apply dvd_pow
  norm_num
  simp_all only [ne_eq,
    not_false_eq_true]

theorem mathd_algebra_251
  (x : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : 3 + 1 / x = 7 / x) :
  x = 2 :=
by
  field_simp [h₀] at h₁
  linarith

theorem mathd_numbertheory_84 :
  Int.floor ((9:ℝ) / 160 * 100) = 5 :=
by
  rw [Int.floor_eq_iff]
  constructor
  all_goals { norm_num }

theorem mathd_algebra_181
  (n : ℝ)
  (h₀ : n ≠ 3)
  (h₁ : (n + 5) / (n - 3) = 2) : n = 11 :=
by
  rw [div_eq_iff] at h₁
  linarith
  exact sub_ne_zero.mpr h₀

theorem algebra_sqineq_2unitcircatblt1
  (a b : ℝ)
  (h₀ : a^2 + b^2 = 2) :
  a * b ≤ 1 :=
by
  have hu := sq_nonneg a
  have hv := sq_nonneg b
  have H₁ := add_nonneg hu hv
  have H₂ : 0 ≤ (a - b) ^ 2 := by nlinarith
  nlinarith

theorem mathd_numbertheory_202 :
  (19^19 + 99^99) % 10 = 8 :=
by
  simp_all only [reducePow,
    reduceAdd,
    reduceMod]

theorem mathd_algebra_51
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a + b = 35)
  (h₂ : a = (2/5) * b) :
  b - a = 15 :=
by
  linarith

theorem mathd_algebra_10 :
  abs ((120 : ℝ)/100 * 30 - 130/100 * 20) = 10 :=
by
  norm_num
