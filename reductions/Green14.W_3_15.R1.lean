import FormalConjectures.GreensOpenProblems.«14»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/


/-!
# Extending a two-coloring by one position

Positions are indexed from zero. At length 217, the coloring in Tanbir
Ahmed, Some New Van der Waerden Numbers and Some Van der Waerden-Type
Numbers, Integers 9 (2009), Table 1, avoids both forbidden progressions.
The bit at index i is set exactly when position i+1 has color 1 in that
table. The kernel checks the two avoidance claims below.

It remains to show separately that every admissible prefix blocks each of
the two possible colors of its next position. The endpoint argument is
adapted from MrSeizy’s Green14.W_3_16.R1, including the interval lemmas
adapted there from Halldon and Dominic Dabish.
-/

open Set Green14
open scoped Classical

namespace OMA.R_Green14_W_3_15_R1

/-- Every admissible prefix has a progression which blocks a red extension. -/
def H1 : Prop :=
  ∀ r : Fin 217 → Bool,
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 109, 0 < d.val ∧ ∀ t : Fin 2,
      r (Fin.ofNat 217 (217 - (2 - t.val) * d.val)) = true

/-- Every admissible prefix has a progression which blocks a blue extension. -/
def H2 : Prop :=
  ∀ r : Fin 217 → Bool,
    (∀ a d : Fin 217, 0 < d.val → a.val + 2 * d.val < 217 →
      ¬ ∀ t : Fin 3, r (Fin.ofNat 217 (a.val + t.val * d.val)) = true) →
    (∀ a d : Fin 217, 0 < d.val → a.val + 14 * d.val < 217 →
      ¬ ∀ t : Fin 15, r (Fin.ofNat 217 (a.val + t.val * d.val)) = false) →
    ∃ d : Fin 16, 0 < d.val ∧ ∀ t : Fin 14,
      r (Fin.ofNat 217 (217 - (14 - t.val) * d.val)) = false

theorem mixedMonoAPGuaranteeSet_upward (k r : ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ mixedMonoAPGuaranteeSet k r) :
    N ∈ mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let emb : Icc 1 M ↪ Icc 1 N :=
    ⟨fun x ↦ ⟨x, x.2.1, x.2.2.trans hMN⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : Icc 1 N ↦ (z : Nat)) h⟩
  let restricted : Icc 1 M → Fin 2 := fun x ↦ coloring (emb x)
  rcases hM restricted with hzero | hone
  · left
    rcases hzero with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy
  · right
    rcases hone with ⟨s, hsAP, hsColor⟩
    let t : Finset (Icc 1 N) := s.map emb
    have hsets : ({(x : Nat) | x ∈ t} : Set Nat) = {(x : Nat) | x ∈ s} := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
        exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨emb y,Finset.mem_map.mpr ⟨y,hy,rfl⟩,rfl⟩
    refine ⟨t, ?_, ?_⟩
    · rw [hsets]
      exact hsAP
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [restricted] using hsColor y hy

/-- One bad coloring of `{1, ..., N}` proves the numerical lower bound
`W(k,r) ≥ N+1`. -/
private theorem W_ge_succ_of_not_mem (k r N : ℕ)
    (hne : (mixedMonoAPGuaranteeSet k r).Nonempty) (hbad : N ∉ mixedMonoAPGuaranteeSet k r) :
    N + 1 ≤ W k r := by
  rw [W]
  apply le_csInf hne
  intro b hb
  by_contra hle
  have hbN : b ≤ N := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hle)
  exact hbad (mixedMonoAPGuaranteeSet_upward k r hbN hb)

private lemma progression_at {N k a d : Nat} (hd : 0 < d)
    (c : Icc 1 N → Fin 2) (color : Fin 2)
    (bound : ∀ i : Fin k, a+i.val*d < N)
    (mono : ∀ (i : Fin k) (hi : a+i.val*d < N), c ⟨a+i.val*d+1, by constructor <;> omega⟩ = color) :
    ∃ s : Finset (Icc 1 N), ({(z : Nat) | z ∈ s}).IsAPOfLength k ∧
      ∀ z ∈ s, c z = color := by
  classical
  let value (i : Fin k) := a + i.val*d + 1
  have inj : Function.Injective value := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (by simpa [value] using h)
  let point : Fin k ↪ Icc 1 N := ⟨fun i => ⟨value i, by
    have := bound i
    dsimp [value]
    constructor <;> omega⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  let s := Finset.univ.map point
  have eqs : ({(z : Nat) | z ∈ s} : Set Nat) = range value := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨point i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [eqs]
    refine ⟨a+1,d,?_,?_⟩
    · rw [ENat.card_coe_set_eq, ← Set.image_univ, inj.encard_image]
      simp
    · ext z
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,by exact_mod_cast i.isLt,by simp [value]; omega⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,by exact_mod_cast hi⟩,by simp [value]; omega⟩
  · intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact mono i (bound i)


private lemma extract_progression {N k : ℕ} (hk : 2 ≤ k) (q : ℕ → Fin 2) (col : Fin 2)
    (h : ∃ s : Finset (Icc 1 N), ({(x : ℕ) | x ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, q (x.val-1) = col) :
    ∃ a d : Fin N, 0 < d.val ∧ a.val + (k-1)*d.val < N ∧
      ∀ i : Fin k, q (a.val + i.val*d.val) = col := by
  obtain ⟨s,⟨a,d,hcard,hset⟩,hc⟩ := h
  have term (i : ℕ) (hi : i < k) :
      ∃ x ∈ s, (x : ℕ) = a + i*d := by
    change a + i*d ∈ ({(x : ℕ) | x ∈ s} : Set ℕ)
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  obtain ⟨x₀, -, hx₀⟩ := term 0 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero] at hx₀
  obtain ⟨x₁, -, hx₁⟩ := term (k-1) (by omega)
  have ha : 1 ≤ a := hx₀ ▸ x₀.property.1
  have hb : a + (k-1)*d ≤ N := hx₁ ▸ x₁.property.2
  have hpos : 0 < d := by
    by_contra! hz
    have hd : d = 0 := by omega
    have heq : ({(x : ℕ) | x ∈ s} : Set ℕ) = {a} := by
      rw [hset]
      ext z
      simp only [hd, nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    have hone : (k : ℕ∞) = 1 := by rw [← hcard, heq]; simp
    have : k = 1 := by exact_mod_cast hone
    omega
  have hd' : d ≤ (k-1)*d := by
    simpa using Nat.mul_le_mul_right d (show 1 ≤ k-1 by omega)
  refine ⟨⟨a-1,by omega⟩,⟨d,by omega⟩,hpos,by change a-1+(k-1)*d < N; omega,?_⟩
  intro i
  obtain ⟨x,hx,hval⟩ := term i.val i.isLt
  have he := hc x hx
  change q (a - 1 + i.val*d) = col
  convert he using 2 <;> omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem lower_witness : 217 ∉ mixedMonoAPGuaranteeSet 3 15 := by
  let q (i : ℕ) : Fin 2 := if (0x4030018020800d05080200404030008840401802100106202200 : ℕ).testBit i then 0 else 1
  have red : ∀ a d : Fin 217, 0 < d.val → a.val + 2*d.val < 217 →
      ¬ ∀ i : Fin 3, q (a.val + i.val*d.val) = 0 := by decide +kernel
  have blue : ∀ a d : Fin 217, 0 < d.val → a.val + 14*d.val < 217 →
      ¬ ∀ i : Fin 15, q (a.val + i.val*d.val) = 1 := by decide +kernel
  intro h
  rcases h (fun x => q (x.val-1)) with hr | hb
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 3) q 0 hr
    exact red a d hd hbound hc
  · obtain ⟨a,d,hd,hbound,hc⟩ := extract_progression (by decide : 2 ≤ 15) q 1 hb
    exact blue a d hd hbound hc

theorem main : H1 → H2 → type_of% @Green14.W_3_15 := by
  intro blockRed blockBlue
  have upper : 218 ∈ mixedMonoAPGuaranteeSet 3 15 := by
    intro c
    by_contra bad
    let color (n : ℕ) := c ⟨n % 218 + 1, by have := Nat.mod_lt n (by decide : 0 < 218); constructor <;> omega⟩
    let red (n : ℕ) := decide (color n = 0)
    let initialColors (i : Fin 217) := red i.val
    have liftAP {k a d : ℕ} (v : Fin 2) (hd : 0 < d) (he : a + (k-1)*d < 218)
        (h : ∀ t : Fin k, color (a+t.val*d) = v) :
        ∃ s : Finset (Icc 1 218), ({(z : ℕ) | z ∈ s} : Set ℕ).IsAPOfLength k ∧
          ∀ z ∈ s, c z = v := by
      apply progression_at (a := a) hd c v
      · intro i
        have := Nat.mul_le_mul_right d (show i.val ≤ k - 1 by omega)
        omega
      · intro i hi
        simpa only [color, Nat.mod_eq_of_lt hi] using h i
    have noRed (a d : ℕ) (hd : 0 < d) (he : a + 2*d < 218) :
        ¬ ∀ t : Fin 3, red (a+t.val*d) = true := by
      intro h
      exact bad (Or.inl (liftAP (k := 3) 0 hd he (fun t => of_decide_eq_true (h t))))
    have noBlue (a d : ℕ) (hd : 0 < d) (he : a + 14*d < 218) :
        ¬ ∀ t : Fin 15, red (a+t.val*d) = false := by
      intro h
      apply bad
      right
      apply liftAP (k := 15) 1 hd he
      intro t
      have hn : color (a+t.val*d) ≠ 0 := of_decide_eq_false (h t)
      exact (show ∀ v : Fin 2, v ≠ 0 → v = 1 by decide) _ hn
    have restrict {k : ℕ} {b : Bool}
        (avoid : ∀ a d : ℕ, 0 < d → a + (k-1)*d < 218 →
          ¬ ∀ t : Fin k, red (a+t.val*d) = b) :
        ∀ a d : Fin 217, 0 < d.val → a.val + (k-1)*d.val < 217 →
          ¬ ∀ t : Fin k, initialColors (Fin.ofNat 217 (a.val+t.val*d.val)) = b := by
      intro a d hd he h
      apply avoid a d hd (by omega)
      intro t
      have := Nat.mul_le_mul_right d.val (show t.val ≤ k-1 by omega)
      have hi : a.val + t.val*d.val < 217 := by omega
      have ht := h t
      change red ((a.val + t.val*d.val) % 217) = b at ht
      rwa [Nat.mod_eq_of_lt hi] at ht
    have extend {m d : ℕ} {b : Bool} (hd : 0 < d) (hb : m*d ≤ 217)
        (prior : ∀ t : Fin m, initialColors (Fin.ofNat 217 (217 - (m-t.val)*d)) = b)
        (last : red 217 = b) :
        ∀ t : Fin (m+1), red (217 - m*d + t.val*d) = b := by
      intro t
      by_cases eq : t.val = m
      · rwa [eq, Nat.sub_add_cancel hb]
      · have lt : t.val < m := by omega
        have hmul := Nat.mul_lt_mul_of_pos_right lt hd
        have hi : 217 - (m-t.val)*d < 217 := by rw [Nat.sub_mul]; omega
        have hx := prior ⟨t.val,lt⟩
        change red ((217-(m-t.val)*d) % 217) = b at hx
        rwa [Nat.mod_eq_of_lt hi, Nat.sub_mul,
          show 217 - (m*d-t.val*d) = 217-m*d+t.val*d by omega] at hx
    cases last : red 217 with
    | true =>
      obtain ⟨d, hd, prev⟩ := blockRed initialColors (restrict (k := 3) noRed) (restrict (k := 15) noBlue)
      have hb : 2*d.val ≤ 217 := by omega
      exact noRed (217-2*d.val) d.val hd (by omega) (extend hd hb prev last)
    | false =>
      obtain ⟨d, hd, prev⟩ := blockBlue initialColors (restrict (k := 3) noRed) (restrict (k := 15) noBlue)
      have hb : 14*d.val ≤ 217 := by omega
      exact noBlue (217-14*d.val) d.val hd (by omega) (extend hd hb prev last)
  exact le_antisymm (Nat.sInf_le upper)
    (W_ge_succ_of_not_mem 3 15 217 ⟨218, upper⟩ lower_witness)

end OMA.R_Green14_W_3_15_R1
