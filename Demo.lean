import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Function

import Smt
import Smt.Real
import Smt.Auto

-- Uninterpreted Functions

-- set_option trace.smt true in
-- set_option trace.smt.solve true in
-- set_option trace.smt.reconstruct.proof true in
example [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
  (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [h0, h1, h2, h3, h4]

-- Linear real arithmetic (copied from linarith)

example (x y z : Real) (h1 : 2*x < 3*y) (h2 : -4*x + z/2 < 0)
        (h3 : 12*y - z < 0) : False := by
  smt [h1, h2, h3]

-- Quantifiers

theorem extracted_1 (n a r v : Type)
  [Nonempty n] [Nonempty a] [Nonempty r] [Nonempty v]
  (b : a → Prop)
  (nmm : a → n → Prop) (ne ngt nm : n → Prop)
  (nsih : ∀ (s1 s2 : n), ∃ a, nmm a s1 ∧ nmm a s2 ∧ ¬b a)
  (noh : ∀ (s : n), ngt s → ∃ a, nmm a s ∧ ¬b a)
  (nsg : ∀ (s : n), nm s → ngt s)
  (nne : ∀ (s : n), ngt s → ¬ne s)
  (sa : a → a → r → v → Prop)
  (sb sc : a → a → a → r → v → Prop) (sg : a → r → Prop)
  (sd se sf : a → a → r → v → Prop)
  (ha :
    (∀ (s d₁ d₂ : a) (r : r) (v₁ v₂ : v),
        ¬b d₁ ∧ ¬b d₂ ∧ sf d₁ s r v₁ ∧ sf d₂ s r v₂ → v₁ = v₂) ∧
      (∀ (s d : a) (r : r) (v : v),
          ¬b s ∧ ¬b d ∧ sf d s r v →
            sg s r ∧ ∀ (d : a), sa s d r v) ∧
        (∀ (s d : a) (r : r) (v : v),
            ¬b s ∧ ¬b d ∧ se d s r v →
              sg s r ∧ ∀ (d : a), sa s d r v) ∧
          (∀ (s o d₁ d₂ : a) (r : r) (v₁ v₂ : v),
              ¬b s → sc s d₁ o r v₁ ∧ sc s d₂ o r v₂ → v₁ = v₂) ∧
            (∀ (s o d₁ d₂ : a) (r : r) (v₁ v₂ : v),
                ¬b s → sb s d₁ o r v₁ ∧ sb s d₂ o r v₂ → v₁ = v₂) ∧
              (∀ (s d₁ d₂ : a) (r : r) (v₁ v₂ : v),
                  ¬b s → sa s d₁ r v₁ ∧ sa s d₂ r v₂ → v₁ = v₂) ∧
                (∀ (s d : a) (r : r) (v : v),
                    ¬b s → ((∀ (d : a), sa s d r v) ↔ sa s d r v)) ∧
                  (∀ (n o : a) (r : r) (v : v),
                      ¬b n →
                        sf n o r v →
                          ∃ q,
                            nm q ∧
                              ∀ (s : a), nmm s q → sc s n o r v) ∧
                    (∀ (n o : a) (r : r) (v : v),
                        ¬b n →
                          se n o r v →
                            (∃ q,
                                nm q ∧
                                  ∀ (s : a), nmm s q → sb s n o r v) ∨
                              ∃ q,
                                ngt q ∧
                                  ∀ (s : a), nmm s q → sc s n o r v) ∧
                      (∀ (n d o : a) (r : r) (v : v),
                          ¬b n → (se n o r v ↔ sc n d o r v)) ∧
                        (∀ (n o : a) (r : r) (v : v),
                            ¬b n → sd n o r v → sa o n r v) ∧
                          (∀ (n d o : a) (r : r) (v : v),
                              ¬b n → (sd n o r v ↔ sb n d o r v)) ∧
                            ∀ (s : a) (r : r),
                              ¬b s → (sg s r ↔ ∃ v, ∀ (d : a), sa s d r v))
  (ta : a → a → r → v → Prop)
  (tb tc : a → a → a → r → v → Prop) (tg : a → r → Prop)
  (td te tf : a → a → r → v → Prop)
  (hb :
    (∀ (s d : a) (r : r) (v : v),
        ¬b s ∧ (sa s d r v ↔ ta s d r v) ∨
          b s ∧ (sa s d r v → ta s d r v)) ∧
      (∀ (s d o : a) (r : r) (v : v),
          ¬b s ∧ (sb s d o r v ↔ tb s d o r v) ∨
            b s ∧ (sb s d o r v → tb s d o r v)) ∧
        (∀ (s d o : a) (r : r) (v : v),
            ¬b s ∧ (sc s d o r v ↔ tc s d o r v) ∨
              b s ∧ (sc s d o r v → tc s d o r v)) ∧
          (∀ (a_2 : a) (a_3 : r), sg a_2 a_3 = tg a_2 a_3) ∧
            (∀ (a_2 a_3 : a) (a_4 : r) (a_5 : v),
                sd a_2 a_3 a_4 a_5 = td a_2 a_3 a_4 a_5) ∧
              (∀ (a_2 a_3 : a) (a_4 : r) (a_5 : v),
                  se a_2 a_3 a_4 a_5 = te a_2 a_3 a_4 a_5) ∧
                ∀ (a_2 a_3 : a) (a_4 : r) (a_5 : v),
                  sf a_2 a_3 a_4 a_5 = tf a_2 a_3 a_4 a_5)
  (n o : a) (r : r) (v : v) :
  ¬b n →
    te n o r v →
      (∃ q, nm q ∧ ∀ (s : a), nmm s q → tb s n o r v) ∨
        ∃ q,
          ngt q ∧ ∀ (s : a), nmm s q → tc s n o r v := by
  smt [nsih, noh, nsg, nne, ha, hb] -- stress test!!!

-- Groups

section

variable [Nonempty G] (op : G → G → G) (inv : G → G) (e : G)

axiom assoc   : ∀ a b c, op a (op b c) = op (op a b) c
axiom inverse : ∀ a, op (inv a) a = e
axiom ident   : ∀ a, op e a = a

-- Group example in slides: NO preprocessing!
-- set_option trace.smt true in
-- set_option trace.smt.solve true in
-- set_option trace.smt.reconstruct.proof true in
theorem unique_identity' {inv : G → G} : ∀ e', (∀ a, op e' a = a) = (e' = e) := by
  smt [assoc op, inverse op inv e, ident op e]

end

-- Integration with Lean Auto!

set_option auto.native true

variable [Group G] -- Type class defined in Mathlib

-- Group example in slides: with preprocessing!
theorem unique_identity : ∀ (e : G), (∀ a, e * a = a) ↔ e = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]

-- Other group lemmas

theorem inverse' : ∀ (a : G), a * a⁻¹ = 1 := by
  auto [mul_assoc, one_mul, inv_mul_cancel]

theorem identity' : ∀ (a : G), a * 1 = a := by
  auto [mul_assoc, one_mul, inv_mul_cancel, inverse']

set_option auto.mono.mode "fol"
set_option auto.mono.ciInstDefEq.mode "reducible"
set_option auto.mono.termLikeDefEq.mode "reducible"

-- Set theory

variable [Nonempty α] [Nonempty β] {f : α → β} {s : Set α} {v u : Set β}

-- The image of the preimage of a set is a subset of that set!
example : f '' (f ⁻¹' u) ⊆ u := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

-- Other set theory lemmas

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage]

example (h : Function.Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  auto [Set.subset_def, Set.mem_preimage, Function.Injective.mem_set_image, h]

example (h : Function.Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  unfold Function.Surjective at h
  auto [Set.subset_def, Set.mem_image, Set.mem_preimage, h]
