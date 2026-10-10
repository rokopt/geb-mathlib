/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.Expansion
public import Geb.Prototypes.LF.Metatheory.Strengthen
public import Geb.Prototypes.LF.Topos.Adequacy
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The compositionality of the decoding of the internal language

The decoding of the canonical LF terms of the fragment commutes with renaming and with
hereditary substitution, the adequacy of a representation being compositional
({cite}`HarperLicata2007`, Section 3.2): decoding a renamed term renames the decoded term, and
decoding a substituted term substitutes the decoded terms. A canonical term of a family of
terms mentions no variable of a family of proofs, the products of the signature's families of
terms ranging over terms alone ({cite}`HarperLicata2007`, Section 2.4, for subordination).

## Main statements

* {lit}`encTy_decTy` — the decodings of types are encoded by their decodings.
* {lit}`dec_rename` — decoding commutes with renaming.
* {lit}`dec_hsub` — decoding commutes with hereditary substitution.
* {lit}`judge_occursOnly` — a term checked against a family of terms mentions only variables of
  families of types and of terms.

## References

* {cite}`HarperLicata2007`, Sections 2.4 and 3.2.

## Tags

logical framework, LF, adequacy, compositionality, substitution, subordination
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term)

/-- The decodings of types are encoded by their decodings. -/
theorem encTy_decTy : ∀ (A : Expr) (a : PartialHorn.Tree), decTy A = some a → encTy a = some A :=
  RoseTree.ind fun l cs ih a h ↦ by
    rw [decTy_node] at h
    rcases l with _ | _ | _ | (i | c)
    · exact absurd h (by simp [decTyStep])
    · exact absurd h (by simp [decTyStep])
    · exact absurd h (by simp [decTyStep])
    · exact absurd h (by simp [decTyStep])
    · unfold decTyStep at h
      split at h
      · next heq hcs =>
        cases heq
        obtain rfl := List.map_eq_nil_iff.mp hcs
        obtain rfl := Option.some.inj h
        rfl
      · next x y heq hcs =>
        cases heq
        obtain ⟨A₁, cs, rfl, hA₁, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain ⟨A₂, cs, rfl, hA₂, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain rfl := List.map_eq_nil_iff.mp hcs
        subst hA₁ hA₂
        obtain ⟨a₁, ha₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨a₂, ha₂, h⟩ := Option.bind_eq_some_iff.mp h
        obtain rfl := Option.some.inj h
        rw [encTy_prod, ih A₁ (by simp) a₁ ha₁, ih A₂ (by simp) a₂ ha₂]
        rfl
      · next x y heq hcs =>
        cases heq
        obtain ⟨A₁, cs, rfl, hA₁, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain ⟨A₂, cs, rfl, hA₂, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain rfl := List.map_eq_nil_iff.mp hcs
        subst hA₁ hA₂
        obtain ⟨a₁, ha₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨a₂, ha₂, h⟩ := Option.bind_eq_some_iff.mp h
        obtain rfl := Option.some.inj h
        rw [encTy_exp, ih A₁ (by simp) a₁ ha₁, ih A₂ (by simp) a₂ ha₂]
        rfl
      · next heq hcs =>
        cases heq
        obtain rfl := List.map_eq_nil_iff.mp hcs
        obtain rfl := Option.some.inj h
        rfl
      · next heq hcs =>
        cases heq
        obtain rfl := List.map_eq_nil_iff.mp hcs
        obtain rfl := Option.some.inj h
        rfl
      · next x heq hcs =>
        cases heq
        obtain ⟨A₁, cs, rfl, hA₁, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain rfl := List.map_eq_nil_iff.mp hcs
        subst hA₁
        obtain ⟨a₁, ha₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain rfl := Option.some.inj h
        rw [encTy_list, ih A₁ (by simp) a₁ ha₁]
        rfl
      · next heq hcs =>
        cases heq
        obtain rfl := List.map_eq_nil_iff.mp hcs
        obtain rfl := Option.some.inj h
        rfl
      · next x heq hcs =>
        cases heq
        obtain ⟨A₁, cs, rfl, hA₁, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain rfl := List.map_eq_nil_iff.mp hcs
        subst hA₁
        obtain ⟨a₁, ha₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain rfl := Option.some.inj h
        rw [encTy_lrose, ih A₁ (by simp) a₁ ha₁]
        rfl
      · next heq hcs =>
        cases heq
        obtain rfl := List.map_eq_nil_iff.mp hcs
        obtain rfl := Option.some.inj h
        rfl
      · next x y heq hcs =>
        cases heq
        obtain ⟨A₁, cs, rfl, hA₁, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain ⟨A₂, cs, rfl, hA₂, hcs⟩ := List.map_eq_cons_iff.mp hcs
        obtain rfl := List.map_eq_nil_iff.mp hcs
        subst hA₁ hA₂
        obtain ⟨a₁, ha₁, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨a₂, ha₂, h⟩ := Option.bind_eq_some_iff.mp h
        obtain rfl := Option.some.inj h
        rw [encTy_coprod, ih A₁ (by simp) a₁ ha₁, ih A₂ (by simp) a₂ ha₂]
        rfl
      · exact absurd h (by simp)

/-- The decodings of types are closed. -/
theorem decTy_closed {A : Expr} {a : PartialHorn.Tree} (h : decTy A = some a) :
    Expr.FreeBelow A 0 = true :=
  encTy_closed a A (encTy_decTy A a h)

variable {k : PrimIdx}

/-- Renaming under a binder in the internal language is renaming under a binder in LF. -/
theorem term_liftR_eq (ρ : ℕ → ℕ) : Term.liftR ρ = liftR ρ := funext fun i ↦ by cases i <;> rfl

/-- Renaming a node of LF applies the renaming lifted under the node's binders to each child; the
children of an application are renamed alike. -/
theorem rename_app_node (h : Head) (cs : List Expr) (ρ : ℕ → ℕ) :
    Expr.rename (RoseTree.node (.app h) cs) ρ =
      RoseTree.node (.app (h.rename ρ)) (cs.map fun c ↦ Expr.rename c ρ) := by
  rw [rename_node]
  exact congrArg _ (List.ext_getElem (by simp) fun k _ _ ↦ by simp [Label.binders])

/-- The children of a node, recovered from their pairing with their decodings. -/
theorem map_dec_eq {cs : List Expr} {ps : List (Expr × Option MTerm)}
    (h : cs.map (fun c ↦ (c, dec k c)) = ps) :
    cs = ps.map Prod.fst ∧ ∀ p ∈ ps, dec k p.1 = p.2 := by
  subst h
  refine ⟨by rw [List.map_map]; exact (List.map_id' cs).symm, fun p hp ↦ ?_⟩
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
  rfl

/-- The replacement of an abstraction's type commutes with renaming. -/
theorem relam_rename {a : PartialHorn.Tree} {s r : MTerm} (h : relam a s = some r)
    (ρ : ℕ → ℕ) : relam a (Term.rename s ρ) = some (Term.rename r ρ) := by
  obtain ⟨a', b, rfl, rfl⟩ := relam_eq_some.mp h
  rfl

/-- The body of a renamed abstraction is its body renamed under the binder. -/
theorem lamBody_rename {s b : MTerm} (h : lamBody s = some b) (ρ : ℕ → ℕ) :
    lamBody (Term.rename s ρ) = some (Term.rename b (Term.liftR ρ)) := by
  obtain ⟨a, rfl⟩ := lamBody_eq_some.mp h
  rfl

/-- Decoding commutes with renaming. -/
theorem dec_rename : ∀ (e : Expr) (ρ : ℕ → ℕ) (s : MTerm), dec k e = some s →
    dec k (e.rename ρ) = some (Term.rename s ρ) :=
  RoseTree.ind fun l cs ih ρ s h ↦ by
    rw [dec_node] at h
    unfold decStep at h
    split at h
    · next _ _ i heq =>
      obtain ⟨rfl, -⟩ := map_dec_eq heq
      obtain rfl := Option.some.inj h
      rfl
    · next _ _ heq =>
      obtain ⟨rfl, -⟩ := map_dec_eq heq
      obtain rfl := Option.some.inj h
      rfl
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      have hu := ih u (by simp) ρ su (hd (u, some su) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
        rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, hu, Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ A dA p₂ f df heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      subst hsf
      have hf := ih f (by simp) ρ sf (hd (f, some sf) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, hf,
        rename_closed (decTy_closed ha), ha, Option.bind_eq_bind, Option.bind_some]
      exact relam_rename h ρ
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      have hu := ih u (by simp) ρ su (hd (u, some su) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
        rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, hu, Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ A dA z dz f df m dm heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨sz, hsz, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sm, hsm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsm hsz hsf
      have hz := ih z (by simp) ρ sz (hd (z, some sz) (by simp))
      have hf := ih f (by simp) ρ sf (hd (f, some sf) (by simp))
      have hm := ih m (by simp) ρ sm (hd (m, some sm) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
        rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, hz, hf, hm,
        lamBody_rename hr ρ, Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ p₁ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      have hu := ih u (by simp) ρ su (hd (u, some su) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, hu, Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht,
        rename_closed (decTy_closed ha), ha, Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht,
        rename_closed (decTy_closed ha), ha, Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA C dC z dz f df m dm heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨sz, hsz, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sm, hsm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsm hsz hsf
      have hz := ih z (by simp) ρ sz (hd (z, some sz) (by simp))
      have hf := ih f (by simp) ρ sf (hd (f, some sf) (by simp))
      have hm := ih m (by simp) ρ sm (hd (m, some sm) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
        rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, hz, hf, hm,
        lamBody_rename hr₁ ρ, lamBody_rename hr (Term.liftR ρ), Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht, Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ C dC f df t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsf hst
      have hf := ih f (by simp) ρ sf (hd (f, some sf) (by simp))
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, hf, ht,
        rename_closed (decTy_closed hc), hc, lamBody_rename hr ρ, Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht,
        rename_closed (decTy_closed ha), ha, Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A C dC f df t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsf hst
      have hf := ih f (by simp) ρ sf (hd (f, some sf) (by simp))
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
        rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, hf, ht,
        rename_closed (decTy_closed hc), hc, lamBody_rename hr ρ, Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA B dB t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht,
        rename_closed (decTy_closed ha), rename_closed (decTy_closed hb), ha, hb,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA B dB t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      have ht := ih t (by simp) ρ st (hd (t, some st) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, ht,
        rename_closed (decTy_closed ha), rename_closed (decTy_closed hb), ha, hb,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA B dB C dC p dp heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sp, hsp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsp
      have hp := ih p (by simp) ρ sp (hd (p, some sp) (by simp))
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
        rename_app_node, dec_node]
      simp only [List.map_cons, List.map_nil, Head.rename, decStep, hp,
        rename_closed (decTy_closed ha), rename_closed (decTy_closed hb),
        rename_closed (decTy_closed hc), ha, hb, hc, Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ b db heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hsb
      have hb := ih b (by simp) (liftR ρ) sb (hd (b, some sb) (by simp))
      rw [List.map_cons, List.map_nil, rename_node, dec_node]
      simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, Label.rename,
        Label.binders, Function.iterate_one, zero_add, decStep, hb, Option.map_eq_map,
        Option.map_some]
      rfl
    · exact absurd h (by simp)

/-- The substitution of a term for the variable of index {lit}`j` of the internal language, the
variables above it lowered by one: the counterpart of LF's hereditary substitution at a base
type. -/
def substAt (j : ℕ) (u : MTerm) : ℕ → MTerm := fun i ↦
  if i < j then Term.var i else if i = j then u else Term.var (i - 1)

/-- The substitution for a variable, lifted under a binder, is the substitution of the term
weakened for the variable above it. -/
theorem liftS_substAt (j : ℕ) (u : MTerm) :
    Term.liftS (substAt j u) = substAt (j + 1) (Term.rename u Nat.succ) := by
  funext i
  rcases i with _ | i
  · simp [Term.liftS, substAt]
  · simp only [Term.liftS, substAt]
    by_cases hij : i < j
    · simp only [hij, ↓reduceIte, show i + 1 < j + 1 by omega]
      rfl
    · by_cases hij' : i = j
      · subst hij'
        simp
      · simp only [hij, ↓reduceIte, hij', show ¬i + 1 < j + 1 by omega,
          show ¬i + 1 = j + 1 by omega]
        rw [show i + 1 - 1 = (i - 1) + 1 by omega]
        rfl

/-- The reduction of a term against the empty spine, where it has a value, is the term. -/
theorem reduce_nil {α : SimpleTy} {n r : Expr} (h : reduce α n [] = some r) : r = n := by
  rw [← RoseTree.node_label_children α, reduce_node] at h
  unfold reduceStep at h
  split at h
  · exact (Option.some.inj h).symm
  · next heq => exact absurd heq (by simp)
  · exact absurd h (by simp)

/-- The children of an application, substituted into, one at a time. -/
theorem mapM_hsub_eq {α : SimpleTy} {n : Expr} {j : ℕ} {cs cs' : List Expr}
    (h : (cs.map fun m ↦ hsub α n m j).mapM id = some cs') :
    cs'.length = cs.length ∧ ∀ (k : ℕ) (h₁ : k < cs.length) (h₂ : k < cs'.length),
      hsub α n cs[k] j = some cs'[k] := by
  obtain ⟨hl, hk⟩ := getElem_of_mapM_id_eq_some h
  refine ⟨by simpa using hl.symm, fun k h₁ h₂ ↦ ?_⟩
  have := hk k (by simpa using h₁) h₂
  rwa [List.getElem_map] at this

section Const

variable {α : SimpleTy} {n : Expr} {j c : ℕ} {e' : Expr}

/-- Substitution into a constant applied to one argument. -/
theorem hsub_const₁ {a : Expr} (h : hsub α n (Expr.const c [a]) j = some e') :
    ∃ a', hsub α n a j = some a' ∧ e' = Expr.const c [a'] := by
  rw [hsub_const] at h
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, id, Option.bind_eq_bind,
    Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Option.map_eq_map,
    Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨a', ha', _, rfl, rfl⟩, rfl⟩ := h
  exact ⟨a', ha', rfl⟩

/-- Substitution into a constant applied to three arguments. -/
theorem hsub_const₃ {a b d : Expr} (h : hsub α n (Expr.const c [a, b, d]) j = some e') :
    ∃ a' b' d', hsub α n a j = some a' ∧ hsub α n b j = some b' ∧ hsub α n d j = some d' ∧
      e' = Expr.const c [a', b', d'] := by
  rw [hsub_const] at h
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, id, Option.bind_eq_bind,
    Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Option.map_eq_map,
    Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨a', ha', _, ⟨b', hb', _, ⟨d', hd', _, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  exact ⟨a', b', d', ha', hb', hd', rfl⟩

/-- Substitution into a constant applied to four arguments. -/
theorem hsub_const₄ {a b d f : Expr} (h : hsub α n (Expr.const c [a, b, d, f]) j = some e') :
    ∃ a' b' d' f', hsub α n a j = some a' ∧ hsub α n b j = some b' ∧ hsub α n d j = some d' ∧
      hsub α n f j = some f' ∧ e' = Expr.const c [a', b', d', f'] := by
  rw [hsub_const] at h
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, id, Option.bind_eq_bind,
    Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Option.map_eq_map,
    Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨a', ha', _, ⟨b', hb', _, ⟨d', hd', _, ⟨f', hf', _, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
    rfl⟩ := h
  exact ⟨a', b', d', f', ha', hb', hd', hf', rfl⟩

/-- The substitution into an application of a constant to two arguments. -/
theorem hsub_const₂ {a b : Expr} (h : hsub α n (Expr.const c [a, b]) j = some e') :
    ∃ a' b', hsub α n a j = some a' ∧ hsub α n b j = some b' ∧ e' = Expr.const c [a', b'] := by
  rw [hsub_const] at h
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, id, Option.bind_eq_bind,
    Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Option.map_eq_map,
    Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨a', ha', _, ⟨b', hb', _, rfl, rfl⟩, rfl⟩, rfl⟩ := h
  exact ⟨a', b', ha', hb', rfl⟩

/-- The substitution into an application of a constant to five arguments. -/
theorem hsub_const₅ {a b d f g : Expr} (h : hsub α n (Expr.const c [a, b, d, f, g]) j = some e') :
    ∃ a' b' d' f' g', hsub α n a j = some a' ∧ hsub α n b j = some b' ∧
      hsub α n d j = some d' ∧ hsub α n f j = some f' ∧ hsub α n g j = some g' ∧
      e' = Expr.const c [a', b', d', f', g'] := by
  rw [hsub_const] at h
  simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil, id, Option.bind_eq_bind,
    Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Option.map_eq_map,
    Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨a', ha', _, ⟨b', hb', _, ⟨d', hd', _, ⟨f', hf', _, ⟨g', hg', _, rfl, rfl⟩, rfl⟩,
    rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  exact ⟨a', b', d', f', g', ha', hb', hd', hf', hg', rfl⟩

end Const

/-- The replacement of an abstraction's type commutes with substitution. -/
theorem relam_subst {a : PartialHorn.Tree} {s r : MTerm} (h : relam a s = some r)
    (σ : ℕ → MTerm) : relam a (Term.subst s σ) = some (Term.subst r σ) := by
  obtain ⟨a', b, rfl, rfl⟩ := relam_eq_some.mp h
  rfl

/-- The body of an abstraction with terms substituted is its body with the substitution lifted
under the binder. -/
theorem lamBody_subst {s b : MTerm} (h : lamBody s = some b) (σ : ℕ → MTerm) :
    lamBody (Term.subst s σ) = some (Term.subst b (Term.liftS σ)) := by
  obtain ⟨a, rfl⟩ := lamBody_eq_some.mp h
  rfl

/-- Decoding commutes with hereditary substitution: the decoding of an expression into which a
term is substituted for a variable is the decoded expression with the decoded term substituted
for the variable. -/
theorem dec_hsub (α : SimpleTy) : ∀ (e n : Expr) (j : ℕ) (e' : Expr) (s u : MTerm),
    dec k e = some s → dec k n = some u → hsub α n e j = some e' →
      dec k e' = some (Term.subst s (substAt j u)) :=
  RoseTree.ind fun l cs ih n j e' s w h hn hs ↦ by
    rw [dec_node] at h
    unfold decStep at h
    split at h
    · next _ _ i heq =>
      obtain ⟨rfl, -⟩ := map_dec_eq heq
      simp only [List.map_nil] at hs
      obtain rfl := Option.some.inj h
      rw [show (RoseTree.node (.app (.var i)) [] : Expr) = Expr.var i [] from rfl, hsub_var] at hs
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.bind_some] at hs
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte] at hs
        obtain rfl := reduce_nil hs
        rw [hn]
        change some w = some (substAt i w i)
        simp only [substAt, Nat.lt_irrefl, ↓reduceIte]
      · simp only [hij, ↓reduceIte, Option.some.injEq] at hs
        subst hs
        rw [Expr.var, Expr.app, dec_node]
        simp only [List.map_nil, decStep, Option.some.injEq]
        change Term.var (if j < i then i - 1 else i) =
          if i < j then Term.var i else if i = j then w else Term.var (i - 1)
        by_cases hlt : i < j
        · simp only [show ¬ j < i by omega, hlt, ↓reduceIte]
        · simp only [show j < i by omega, hlt, hij, ↓reduceIte]
    · next _ _ heq =>
      obtain ⟨rfl, -⟩ := map_dec_eq heq
      simp only [List.map_nil] at hs
      obtain rfl := Option.some.inj h
      rw [show (RoseTree.node (.app (.const 7)) [] : Expr) = Expr.const 7 [] from rfl,
        hsub_const] at hs
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.map_eq_map,
        Option.map_some, Option.some.injEq] at hs
      subst hs
      rfl
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      obtain ⟨-, -, t', u', -, -, ht', hu', rfl⟩ := hsub_const₄ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht',
        ih u (by simp) n j u' su w (hd (u, some su) (by simp)) hn hu', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      obtain ⟨-, -, t', -, -, ht', rfl⟩ := hsub_const₃ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      obtain ⟨-, -, t', -, -, ht', rfl⟩ := hsub_const₃ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ A dA p₂ f df heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      subst hsf
      obtain ⟨A', -, f', hA', -, hf', rfl⟩ := hsub_const₃ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed ha), Option.some.injEq] at hA'
      subst hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha,
        ih f (by simp) n j f' sf w (hd (f, some sf) (by simp)) hn hf', Option.bind_eq_bind,
        Option.bind_some]
      exact relam_subst h _
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      obtain ⟨-, -, t', u', -, -, ht', hu', rfl⟩ := hsub_const₄ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht',
        ih u (by simp) n j u' su w (hd (u, some su) (by simp)) hn hu', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      obtain ⟨t', ht', rfl⟩ := hsub_const₁ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      obtain ⟨t', ht', rfl⟩ := hsub_const₁ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ A dA z dz f df m dm heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨sz, hsz, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sm, hsm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsm hsz hsf
      obtain ⟨A', z', f', m', -, hz', hf', hm', rfl⟩ := hsub_const₄ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih z (by simp) n j z' sz w (hd (z, some sz) (by simp)) hn hz',
        ih f (by simp) n j f' sf w (hd (f, some sf) (by simp)) hn hf',
        ih m (by simp) n j m' sm w (hd (m, some sm) (by simp)) hn hm', lamBody_subst hr _,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ p₁ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      obtain ⟨-, t', u', -, ht', hu', rfl⟩ := hsub_const₃ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht',
        ih u (by simp) n j u' su w (hd (u, some su) (by simp)) hn hu', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      obtain ⟨A', t', hA', ht', rfl⟩ := hsub_const₂ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed ha), Option.some.injEq] at hA'
      subst hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      obtain ⟨A', t', hA', ht', rfl⟩ := hsub_const₂ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed ha), Option.some.injEq] at hA'
      subst hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA C dC z dz f df m dm heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨sz, hsz, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sm, hsm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsm hsz hsf
      obtain ⟨A', C', z', f', m', -, -, hz', hf', hm', rfl⟩ := hsub_const₅ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih z (by simp) n j z' sz w (hd (z, some sz) (by simp)) hn hz',
        ih f (by simp) n j f' sf w (hd (f, some sf) (by simp)) hn hf',
        ih m (by simp) n j m' sm w (hd (m, some sm) (by simp)) hn hm', lamBody_subst hr₁ _,
        lamBody_subst hr _, Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      obtain ⟨t', ht', rfl⟩ := hsub_const₁ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ C dC f df t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsf hst
      obtain ⟨C', f', t', hC', hf', ht', rfl⟩ := hsub_const₃ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed hc), Option.some.injEq] at hC'
      subst hC'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, hc,
        ih f (by simp) n j f' sf w (hd (f, some sf) (by simp)) hn hf',
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', lamBody_subst hr _,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      obtain ⟨A', t', hA', ht', rfl⟩ := hsub_const₂ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed ha), Option.some.injEq] at hA'
      subst hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A C dC f df t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsf hst
      obtain ⟨A', C', f', t', -, hC', hf', ht', rfl⟩ := hsub_const₄ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed hc), Option.some.injEq] at hC'
      subst hC'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, hc,
        ih f (by simp) n j f' sf w (hd (f, some sf) (by simp)) hn hf',
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', lamBody_subst hr _,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA B dB t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      obtain ⟨A', B', t', hA', hB', ht', rfl⟩ := hsub_const₃ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed ha), Option.some.injEq] at hA'
      rw [hsub_eq, hsubWith_closed (decTy_closed hb), Option.some.injEq] at hB'
      subst hA' hB'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha, hb,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA B dB t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst
      obtain ⟨A', B', t', hA', hB', ht', rfl⟩ := hsub_const₃ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed ha), Option.some.injEq] at hA'
      rw [hsub_eq, hsubWith_closed (decTy_closed hb), Option.some.injEq] at hB'
      subst hA' hB'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha, hb,
        ih t (by simp) n j t' st w (hd (t, some st) (by simp)) hn ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA B dB C dC p dp heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sp, hsp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsp
      obtain ⟨A', B', C', p', hA', hB', hC', hp', rfl⟩ := hsub_const₄ hs
      rw [hsub_eq, hsubWith_closed (decTy_closed ha), Option.some.injEq] at hA'
      rw [hsub_eq, hsubWith_closed (decTy_closed hb), Option.some.injEq] at hB'
      rw [hsub_eq, hsubWith_closed (decTy_closed hc), Option.some.injEq] at hC'
      subst hA' hB' hC'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha, hb, hc,
        ih p (by simp) n j p' sp w (hd (p, some sp) (by simp)) hn hp', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ b db heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hsb
      rw [show (RoseTree.node Label.lam [b] : Expr) = Expr.lam b from rfl, hsub_lam,
        Option.map_eq_map, Option.map_eq_some_iff] at hs
      obtain ⟨b', hb', rfl⟩ := hs
      have hb := ih b (by simp) n.shift (j + 1) b' sb (Term.rename w Nat.succ)
        (hd (b, some sb) (by simp)) (dec_rename n Nat.succ w hn) hb'
      rw [Expr.lam, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, hb, Option.map_eq_map, Option.map_some,
        ← liftS_substAt]
      rfl
    · exact absurd h (by simp)

section Subordination

/-- Whether a type is the kind of types or a family of terms, after its products: the types whose
inhabitants are the fragment's types and terms. -/
def TermHead (T : Expr) : Bool := T.headDepth.1 == some 0 || T.headDepth.1 == some 6

/-- One step of whether every domain of a type's products is of {name}`Geb.LF.Topos.TermHead` and,
in turn, of this kind. -/
def domsOKStep (l : Label) (cs : List (Expr × Bool)) : Bool :=
  match l, cs with
    | .pi, [(a, ra), (_, rb)] => TermHead a && ra && rb
    | _, _ => true

/-- Whether every domain of a type's products is of {name}`Geb.LF.Topos.TermHead`, and of this
kind in turn: the classifiers whose arguments are types and terms. -/
def Expr.DomsOK : Expr → Bool := RoseTree.para domsOKStep

/-- The computation rule of {name}`Geb.LF.Topos.Expr.DomsOK`. -/
theorem domsOK_node (l : Label) (cs : List Expr) :
    Expr.DomsOK (RoseTree.node l cs) = domsOKStep l (cs.map fun c ↦ (c, Expr.DomsOK c)) :=
  RoseTree.para_node _ l cs

/-- The domains of a product of {name}`Geb.LF.Topos.Expr.DomsOK`. -/
theorem domsOK_pi {a b : Expr} (h : Expr.DomsOK (Expr.pi a b) = true) :
    TermHead a = true ∧ Expr.DomsOK a = true ∧ Expr.DomsOK b = true := by
  rw [show Expr.pi a b = RoseTree.node .pi [a, b] from rfl, domsOK_node] at h
  simpa only [List.map_cons, List.map_nil, domsOKStep, Bool.and_eq_true, and_assoc] using h

/-- Substitution keeps {name}`Geb.LF.Topos.Expr.DomsOK` in an expression of the shape of types,
whatever the reduction. -/
theorem domsOK_hsubWith (red : Expr → List Expr → Option Expr) :
    ∀ (e n : Expr) (j : ℕ) (e' : Expr), Expr.TypeShape e = true → hsubWith red e n j = some e' →
      Expr.DomsOK e' = Expr.DomsOK e :=
  RoseTree.ind fun l cs ih n j e' hs h ↦ by
    rw [typeShape_node] at hs
    rcases l with _ | _ | _ | (i | c)
    · rcases cs with _ | ⟨d, cs⟩
      · rw [hsubWith_node_of_ne _ _ (fun i h ↦ by cases h)] at h
        simp only [List.zipIdx_nil, List.map_nil, List.mapM_nil, Option.pure_def,
          Option.map_eq_map, Option.map_some, Option.some.injEq] at h
        rw [← h]
      · simp [typeShapeStep] at hs
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · simp [typeShapeStep] at hs
      · simp [typeShapeStep] at hs
      · simp only [List.map_cons, List.map_nil, typeShapeStep, Bool.and_eq_true] at hs
        rw [hsubWith_node_of_ne _ _ (fun i h ↦ by cases h), Option.map_eq_map,
          Option.map_eq_some_iff] at h
        obtain ⟨ys, hys, rfl⟩ := h
        rw [mapM_id_eq_some_iff] at hys
        rcases ys with _ | ⟨a', _ | ⟨b', _ | ⟨d', ys⟩⟩⟩
        · simp at hys
        · simp at hys
        · simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
            List.cons.injEq] at hys
          rw [domsOK_node, domsOK_node]
          simp only [List.map_cons, List.map_nil, domsOKStep, TermHead,
            headDepth_hsubWith _ a _ _ _ hs.1 hys.1, ih a (by simp) _ _ _ hs.1 hys.1,
            ih b (by simp) _ _ _ hs.2 hys.2.1]
        · simp at hys
      · simp [typeShapeStep] at hs
    · simp [typeShapeStep] at hs
    · simp [typeShapeStep] at hs
    · rw [hsubWith_node_of_ne _ _ (fun i h ↦ by cases h), Option.map_eq_map,
        Option.map_eq_some_iff] at h
      obtain ⟨ys, -, rfl⟩ := h
      rfl

/-- Renaming keeps {name}`Geb.LF.Topos.Expr.DomsOK`. -/
theorem domsOK_rename : ∀ (e : Expr) (ρ : ℕ → ℕ),
    Expr.DomsOK (e.rename ρ) = Expr.DomsOK e :=
  RoseTree.ind fun l cs ih ρ ↦ by
    rw [rename_node, domsOK_node, domsOK_node]
    rcases l with _ | _ | _ | (i | c)
    · rfl
    · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨d, cs⟩⟩⟩
      · rfl
      · rfl
      · simp only [Label.rename, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
          domsOKStep, Label.binders, Function.iterate_one, Function.iterate_zero_apply, zero_add,
          TermHead, headDepth_rename, ih a (by simp), ih b (by simp)]
      · rfl
    · rfl
    · rfl
    · rfl

/-- The declarations of the signature whose types end in {lit}`tp` or {lit}`tm` take types and
terms as arguments. -/
theorem sig_domsOK {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : TermHead T = true) :
    Expr.DomsOK T = true := by
  have key : (sig.all fun T ↦ !TermHead T || Expr.DomsOK T) = true := by decide +kernel
  rw [List.all_eq_true] at key
  have := key T (List.mem_of_getElem? hc)
  simpa [h] using this

/-- The head of a product is its codomain's. -/
theorem termHead_pi (a b : Expr) : TermHead (Expr.pi a b) = TermHead b := by
  simp only [TermHead, Expr.pi, headDepth_node, List.map_cons, List.map_nil, headDepthStep]

/-- The arguments along which a classifier of the shape of types whose domains are types and terms
instantiates are each checked against a type of the shape whose arguments are types and terms. -/
theorem spine_args_termHead {J : Expr → Ctx → Mode → Bool} {Γ : Ctx} :
    ∀ (ms : List Expr) (c r : Expr), Expr.TypeShape c = true → Expr.DomsOK c = true →
      spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      ∀ m ∈ ms, ∃ a, Expr.TypeShape a = true ∧ TermHead a = true ∧ Expr.DomsOK a = true ∧
        J m Γ (.check a) = true :=
  fun ms ↦ ms.rec (motive := fun ms ↦ ∀ (c r : Expr), Expr.TypeShape c = true →
      Expr.DomsOK c = true → spine Γ c (ms.map fun m ↦ (m, J m)) = some r →
      ∀ m ∈ ms, ∃ a, Expr.TypeShape a = true ∧ TermHead a = true ∧ Expr.DomsOK a = true ∧
        J m Γ (.check a) = true)
    (fun _ _ _ _ _ m hm ↦ absurd hm List.not_mem_nil)
    (fun m ms ih c r hc hd h m' hm' ↦ by
      rw [List.map_cons] at h
      obtain ⟨a, b, c', rfl, hJ, hc', hr⟩ := Geb.LF.spine_cons_inv h
      obtain ⟨ha, hb⟩ := typeShape_pi hc
      obtain ⟨hta, hda, hdb⟩ := domsOK_pi hd
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact ⟨a, ha, hta, hda, hJ⟩
      · refine ih c' r (typeShape_hsubWith _ b m 0 c' hb hc').1 ?_ hr m' hm'
        rw [domsOK_hsubWith _ b m 0 c' hb hc']
        exact hdb)

/-- Terms mention only variables of types and terms (subordination): in an expression checked
against a type of the shape whose arguments are types and terms, ending in {lit}`tp` or
{lit}`tm`, in a context of such types, every variable is of a type ending in {lit}`tp` or
{lit}`tm`. -/
theorem judge_occursOnly : ∀ (e : Expr) (Γ : Ctx) (P : Expr),
    (∀ a ∈ Γ, Expr.TypeShape a = true ∧ Expr.DomsOK a = true) → Expr.TypeShape P = true →
    TermHead P = true → Expr.DomsOK P = true → judge sig e Γ (.check P) = true →
    e.OccursOnly (fun i ↦ (varType Γ i).any TermHead) = true :=
  RoseTree.ind fun l cs ih Γ P hΓ hPs hPh hPd hj ↦ by
    have hvar : ∀ {i : ℕ} {t : Expr}, varType Γ i = some t →
        Expr.TypeShape t = true ∧ Expr.DomsOK t = true := fun {i t} ht ↦ by
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp ht
      obtain ⟨h₁, h₂⟩ := hΓ a (List.mem_of_getElem? ha)
      exact ⟨by rw [typeShape_rename]; exact h₁, by rw [domsOK_rename]; exact h₂⟩
    rw [judge, judgeWith_node] at hj
    rcases l with _ | _ | _ | hd
    · simp [judgeStep] at hj
    · simp [judgeStep] at hj
    · rcases cs with _ | ⟨b, _ | ⟨d, cs⟩⟩
      · simp [judgeStep] at hj
      · obtain ⟨pl, pcs, rfl⟩ := exists_node P
        rcases pl with _ | _ | _ | _
        · simp [judgeStep] at hj
        · rcases pcs with _ | ⟨a, _ | ⟨B, _ | ⟨d', pcs⟩⟩⟩
          · simp [judgeStep] at hj
          · simp [judgeStep] at hj
          · simp only [judgeStep, List.map_cons, List.map_nil, RoseTree.label_node,
              RoseTree.children_node] at hj
            have hPpi : (RoseTree.node Label.pi [a, B] : Expr) = Expr.pi a B := rfl
            rw [hPpi] at hPs hPh hPd
            obtain ⟨has, hBs⟩ := typeShape_pi hPs
            obtain ⟨-, hda, hdB⟩ := domsOK_pi hPd
            rw [termHead_pi] at hPh
            have hΓ' : ∀ x ∈ a :: Γ, Expr.TypeShape x = true ∧ Expr.DomsOK x = true :=
              fun x hx ↦ by
                rcases List.mem_cons.mp hx with rfl | hx
                · exact ⟨has, hda⟩
                · exact hΓ x hx
            have hb := ih b (by simp) (a :: Γ) B hΓ' hBs hPh hdB hj
            refine occursOnly_node_iff.mpr ⟨(fun _ h ↦ nomatch h), fun idx hidx ↦ ?_⟩
            rcases idx with _ | idx
            · refine occursOnly_mono b (fun i hi ↦ ?_) hb
              rcases i with _ | i
              · rfl
              · change (varType Γ i).any TermHead = true
                rw [varType_cons_succ] at hi
                cases hvi : varType Γ i with
                | none => rw [hvi] at hi; exact absurd hi (by simp)
                | some t =>
                  rw [hvi] at hi
                  simpa [TermHead, headDepth_rename] using hi
            · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)
          · simp [judgeStep] at hj
        · simp [judgeStep] at hj
        · simp [judgeStep] at hj
      · simp [judgeStep] at hj
    · simp only [judgeStep, Bool.and_eq_true] at hj
      obtain ⟨hP, hm⟩ := hj
      obtain ⟨C, hC, hS⟩ : ∃ C, classOf sig Γ hd = some C ∧
          spine Γ C (cs.map fun c ↦ (c, judge sig c)) = some P := by
        split at hm
        · next R hR =>
          obtain ⟨C, hC, hS⟩ := Option.bind_eq_some_iff.mp hR
          exact ⟨C, hC, hS.trans (congrArg some (beq_iff_eq.mp hm))⟩
        · exact absurd hm Bool.false_ne_true
      have hCs : Expr.TypeShape C = true := by
        rcases hd with i | c
        · exact (hvar hC).1
        · exact Sig.ok_typeShape sig_ok c C hC
      have hCh : TermHead C = true := by
        have := (spine_headDepth _ C P hCs hS).1
        simpa [TermHead, this] using hPh
      have hCd : Expr.DomsOK C = true := by
        rcases hd with i | c
        · exact (hvar hC).2
        · exact sig_domsOK hC hCh
      refine occursOnly_node_iff.mpr ⟨fun i hi ↦ ?_, fun idx hidx ↦ ?_⟩
      · cases hi
        change classOf sig Γ (.var i) = some C at hC
        rw [show varType Γ i = classOf sig Γ (.var i) from rfl, hC]
        simpa using hCh
      · obtain ⟨a, has, hah, had, haJ⟩ :=
          spine_args_termHead cs C P hCs hCd hS cs[idx] (List.getElem_mem hidx)
        rw [Label.binders_app, Function.iterate_zero_apply]
        exact ih _ (List.getElem_mem hidx) Γ a hΓ has hah had haJ

end Subordination

end Geb.LF.Topos

end
