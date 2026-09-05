import Groebner

/-!
# Extensions intended for Groebner

This module restores the standard-representation form of Buchberger's criterion, which CaseI uses
and which is no longer exported by Groebner's `main` branch.
-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial IsRemainder

/-- A finite representation of `p` by `G` whose nonzero summands have degree below `d`. -/
def HasStandardRepresentation {σ : Type*} {R : Type*} [CommSemiring R]
    (m : MonomialOrder σ) (G : Set (MvPolynomial σ R))
    (p : MvPolynomial σ R) (d : m.syn) : Prop :=
  ∃ q : G →₀ MvPolynomial σ R,
    p = Finsupp.linearCombination _ (fun b : G ↦ b.val) q ∧
      ∀ b : G, q b ≠ 0 → m.toSyn (m.degree (b.val * q b)) < d

namespace IsGroebnerBasis

open scoped MonomialOrder

section CommRing

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

private lemma degree_lt_of_left_ne_zero_of_degree_mul_lt_of_mem_nonZeroDivisors {R} [CommSemiring R]
    {p p' q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : m.leadingCoeff q ∈ nonZeroDivisors _)
    (h : m.degree (p * q) ≺[m] m.degree (p' * q)) :
    m.degree p ≺[m] m.degree p' := by
  apply lt_of_le_of_lt' m.degree_mul_le at h
  simpa [m.degree_mul_of_right_mem_nonZeroDivisors hp hq] using h

private lemma degree_mul_lt_iff_left_lt_of_ne_zero_of_mem_nonZeroDivisors {R}
    [CommSemiring R] {p p' q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : m.leadingCoeff q ∈ nonZeroDivisors _) :
    m.degree (p * q) ≺[m] m.degree (p' * q) ↔ m.degree p ≺[m] m.degree p' := by
  refine ⟨degree_lt_of_left_ne_zero_of_degree_mul_lt_of_mem_nonZeroDivisors hp hq, ?_⟩
  intro h
  simpa [m.degree_mul_of_right_mem_nonZeroDivisors hp hq,
    m.degree_mul_of_right_mem_nonZeroDivisors (show p' ≠ 0 by contrapose! h; simp [h]) hq] using h

set_option maxHeartbeats 400000 in
-- This compatibility proof needs additional elaboration time with the current dependencies.
/-- The standard-representation form of Buchberger's criterion. -/
theorem isGroebnerBasis_of_hasStandardRepresentation_sPolynomial
    {G : Set (MvPolynomial σ R)} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hsPoly : ∀ (g₁ g₂ : G), m.HasStandardRepresentation G
      (m.sPolynomial g₁ g₂ : MvPolynomial σ R)
      (m.toSyn (m.degree g₁.val ⊔ m.degree g₂.val))) :
    m.IsGroebnerBasis G (Ideal.span G) := by
  /- The informal proof is attached in comment blocks (`/- -/`), where math expressions are written
  in `$ $` or `$$ $$` like in LaTeX or Markdown, while we tend to use unicode symbols like Lean code
  instead of LaTeX commands are used for readability. And every block roughly corresponds with a
  block of code below it and above the next comment block (if it exists). And inline comments (`--`)
  are about technical details in formalization. -/
  -- TODO: (maybe) simplify this proof with `withBotDegree`? (The current proof was made before
  -- `withBotDegree` was defined and used to refactor `IsRemainder`, so it deals with some edge
  -- cases about degree of zero polynomial.)
  classical
  /- 
  We only need to prove for all $p ∈ ⟨G⟩$ (`p ∈ Ideal.span G`),
  (without loss of generality, assuming $p ≠ 0$)
  $0$ is a remainder of $p$ on division by $G$ (`m.IsRemainder p G 0`), i.e.
  to prove that there exists a finite subset $G'$ of $G$ and $f$
  s.t. $p = ∑_{g ∈ G'} f(g) * g$ and $∀ g ∈ G', degree(f(g) * g) ≤ degree(p)$. -/
  wlog! _ : Nontrivial R
  · simp
  have hG₁ {g : G} := hG g g.prop
  have hG₀ {g} := (@hG₁ g).mem_nonZeroDivisors
  -- `rfl` doesn't rewrite the goal?
  rw [isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero (hG := hG)]
  exists Ideal.subset_span
  intro p hp
  wlog! hpne0 : p ≠ 0
  · simp [hpne0]
  simp_rw [isRemainder_def, add_zero, ← map_add,
    ← m.withBotDegree_mul_of_left_mem_nonZeroDivisors hG₀,
    m.withBotDegree_le_withBotDegree_iff_of_ne_zero _ hpne0]
  refine ⟨?_, by simp⟩
  /- From $p ∈ ⟨G⟩$, we get immediately that all condition we needed above except for
  $∀ g ∈ G', degree(f(g) * g) ≤ degree(p)$.
  We assume it doesn't hold, i.e. $max_{g ∈ G'} degree(f(g) * g) > degree(p)$. -/
    -- todo: `Ideal.mem_span_iff_exists_finset_subset`?
  obtain ⟨f₀_, G'₀_, hG'_, ⟨-, hsumf⟩⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hp
  -- we need variants of `f₀` and `G'₀` that use coercion `↥G` instead of `MvPolynomial σ R`, to
  -- pass the information of set membership and make use of `hG` and S-polynomial decomposition.
  let G'₀ := G'₀_.attach.image (β := G) (fun p ↦ ⟨p.val, hG'_ p.prop⟩)
  let f₀ (p : G) := f₀_ p
  convert_to ∑ a ∈ G'₀, f₀ a * a = p at hsumf
  · unfold G'₀
    rw [Finset.sum_image (by simp [Function.Injective])]
    exact Finset.sum_attach .. |>.symm
  clear_value G'₀ f₀
  clear hG'_ G'₀_ f₀_
  by_cases! h : G'₀.sup (fun g ↦ (m.toSyn <| m.degree <| g.val * (f₀ g))) ≤ m.toSyn (m.degree p)
  · exact ⟨f₀, G'₀, hsumf.symm, by simpa using h⟩
  /- We have now $P(max_{g ∈ G'} degree(f(g) * g))$ where
  $P(a) : ∃ finite G' ⊆ G and f, p = ∑ g ∈ G', f(g) * g ∧ ∀ g ∈ G', degree(f(g) * g) ≤ a$,
  and we will prove an assertion that, for each $a > degree(p)$, if $P(a)$, then there exists
  $degree(p) ≤ a' < a$ s.t. $P(a')$ also holds. With this assertion, we can get $P(degree(p))$ by
  well-founded induction on $a$.
  (Formalization note: here we don't directly prove $degree(p)$ satisfies predicate $P$ by
   induction. We prove with predicate $a ↦ degree(p) ≤ a ∧ P(a)$ instead.) -/
  -- todo: lemmas for induction in this form.
  refine WellFounded.induction_bot WellFoundedLT.toWellFoundedRelation.wf
    (a := G'₀.sup fun g ↦ (m.toSyn <| m.degree <| g.val * (f₀ g))) (bot := m.toSyn (m.degree p))
    (C := fun a ↦ m.toSyn (m.degree p) ≤ a ∧
      ∃ (f : G → MvPolynomial σ R) (G' : Finset G),
        p = ∑ g ∈ G', (f g) * g ∧
        ∀ g ∈ G', (m.toSyn <| m.degree <| g.val * f g) ≤ a)
    (fun a ha ⟨ha', ⟨f, G', hsumf, h_deg_le⟩⟩ ↦ ?_)
    ⟨le_of_lt h, ⟨f₀, G'₀, hsumf.symm, by apply Finset.le_sup⟩⟩ |>.2
  /- We start to prove the assertion. Assume $a > degree(p)$ (`ha`), $G' : Finset G$,
  $f$ (`f`) s.t. $p = ∑ g ∈ G', f(g) * g$ (`hsumf`), and
  $∀ g ∈ G', degree(f(g) * g) ≤ a$ (`h_deg_le`).
  Without loss of generality, we can assume $f(g)$ vanishes when $g ∉ G'$.  -/
  clear! f₀ G'₀
  wlog hf₀support : ∀ g, g ∉ G' → f g = 0 generalizing f
  · specialize this (fun g ↦ if g ∈ G' then f g else 0); simp_all
  apply lt_of_le_of_ne' ha' at ha
  /- Let $lt'(g) := leadingTerm(f(g)) if degree(f(g) * g) = a, or else 0$ (`lt'`).
  $$ p = ∑ g ∈ G', f(g) * g
       = ∑ g ∈ G' with (degree(f(g) * g) = a), leadingTerm(f(g)) * g +
        ∑ g ∈ G', (f(g) - lt'(g)) * g.$$ (`hp`) -/
  let degFgEqA g := (m.toSyn <| m.degree <| f g * g.val) = a
  let lt' g := if degFgEqA g then m.leadingTerm (f g) else 0
  have hp := calc
    p = ∑ g ∈ G', f g * g := hsumf
    _ = ∑ g ∈ G' with degFgEqA g, m.leadingTerm (f g) * g +
        ∑ g ∈ G', (f g - lt' g) * g := by
      simp [← Finset.sum_add_distrib, ← add_mul, ← ite_zero_mul, Finset.sum_filter, -ite_mul, lt']
  /- For any $g ∈ G'$, removing the leading term when $degree(f(g) * g) = a$ gives
  $degree((f(g) - lt'(g)) * g) < a$. Zero products also satisfy this bound since $0 < a$.
  Thus $degree(∑ g ∈ G', (f(g) - lt'(g)) * g) < a$.
  Since $$degree( ∑ g ∈ G' with (degree(f(g) * g) = a), leadingTerm(f(g)) * g +
      ∑ g ∈ G', (f(g) - lt'(g)) * g )
    = degree(p) < a,$$
  we can obtain $degree( ∑ g ∈ G' with (degree(f(g) * g) = a), leadingTerm(f(g)) * g ) < a$.
  Obviously, $degree(leadingTerm(f(g)) g)) = a$, for all $g ∈ G'$ s.t. $degree(f(g) g) = a$.
  So this sum can be decomposed into a sum of S-polynomials: there exists $c(g₁, g₂) ∈ R$ (`c`)
  for each $g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\}$, s.t.
  $$∑ g ∈ G' with (degree(f(g) * g) = a), leadingTerm(f(g)) * g
    = ∑ g ∈ G' with (degree(f(g) * g) = a), leadingCoeff(f(g)) • lm(f(g)) * g
    = ∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
          c(g₁, g₂) * sPoly(lm(f(g₁)) * g₁, lm(f(g₂)) * g₂)
    = ∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
          c(g₁, g₂) * (lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * sPoly(g₁, g₂),$$
    (`h_sum_sPoly`)
  where $lm(p)$ is leading monomial of $p$ ($x^degree(p)$ if we ignore edge case that $p = 0$),
  and $lcm(lm(g₁), lm(g₂))$ is least common multiple of $lm(g₁)$ and $lm(g₂)$.
  (Formalization note: formalization of $lcm$ is based on operations on `Finsupp` instead of
  `MvPolynomial`. For more formalization details, see the doc of `MonomialOrder.sPolynomial`.) -/
  have h_a_gt_zero : 0 < a := bot_lt_of_lt ha
  let leadingTerm_mul_eq (p q : MvPolynomial σ R) :
      m.leadingTerm p * q = m.leadingCoeff p • (monomial (m.degree p) 1 * q) := by
    rw [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one, leadingTerm]
    -- simp [← mul_assoc]
  obtain ⟨c, h_sum_sPoly⟩ := m.sPolynomial_decomposition_of_degree_sum_smul_le
    (d := a) (B := G'.filter degFgEqA) (g := fun g ↦ monomial (m.degree (f g)) 1 * g.val)
    (c := fun g ↦ m.leadingCoeff (f g))
    (hB := by simp [hG, m.leadingCoeff_mul_of_right_mem_nonZeroDivisors' hG₀])
    (by
      simp only [Finset.mem_filter, and_imp, degFgEqA]
      intro b hb h
      rw [m.degree_mul_of_right_mem_nonZeroDivisors ?_ hG₀]
        at h ⊢
      · simpa [m.degree_monomial] using h
      · simp
      contrapose! h_a_gt_zero with hfb
      simp [← h, hfb])
    (by
      simp only [leadingTerm_mul_eq] at hp
      simp only [← sub_eq_iff_eq_add.mpr hp]
      apply lt_of_le_of_lt m.degree_sub_le
      simp? [ha] says simp only [max_lt_iff, ha, true_and]
      apply lt_of_le_of_lt m.degree_sum_le
      simp only [Finset.sup_lt_iff h_a_gt_zero, lt']
      intro g hg
      wlog h : degFgEqA g
      · simpa [h] using lt_of_le_of_ne (mul_comm g.val _ ▸ h_deg_le g hg) h
      simp? [h] says simp only [h, ↓reduceIte]
      wlog! +distrib h' : f g - m.leadingTerm (f g) ≠ 0
      · simp [h_a_gt_zero, h']
      apply lt_of_le_of_lt' (h_deg_le g hg)
      -- case edge about `degree 0`
      rw [mul_comm g.val, degree_mul_lt_iff_left_lt_of_ne_zero_of_mem_nonZeroDivisors h' hG₀]
      exact m.degree_sub_leadingTerm_lt_degree (m.degree_ne_zero_of_sub_leadingTerm_ne_zero h'))
  conv at h_sum_sPoly =>
    simp only [← leadingTerm_mul_eq]
    rhs
    simp only [m.sPolynomial_monomial_mul_of_mem_nonZeroDivisors hG₀ hG₀,
      ← G'.filter degFgEqA |>.sum_coe_sort]
  /- For each pair $g₁, g₂$ in the filtered set, the standard-representation hypothesis
  supplies a finitely supported function $q_{g₁, g₂} : G →₀ S$ (`q`) such that (`hq`):
    - $sPoly(g₁, g₂) = ∑ g ∈ G, q_{g₁, g₂}(g) * g$;
    - if $q_{g₁, g₂}(g) ≠ 0$, then
      $degree(g * q_{g₁, g₂}(g)) < degree(g₁) ⊔ degree(g₂)$.
  The bound is the least common multiple of the leading monomials. No zero-remainder
  hypothesis or requirement that $q_{g₁, g₂} = 0$ for a zero S-polynomial is used here. -/
  replace hsPoly (g₁ g₂ : G'.filter degFgEqA) := hsPoly g₁ g₂
  let q (g₁ g₂ : G'.filter degFgEqA) := (hsPoly g₁ g₂).choose
  have hq (g₁ g₂ : G'.filter degFgEqA) := (hsPoly g₁ g₂).choose_spec
  -- I'd like to get rid of `.choose` in following formalization.
  simp_rw [show _ = q _ _ by unfold q; rfl] at hq
  -- TODO: a variant of `generalize` tactic that can replace with arguments
  clear_value q -- clear its value to ensure we will not use it (optional)
  /- Let $G''$ be $G' ∪ (∪ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\}, supp(q_{g₁, g₂})).$
  Obviously, $G''$ is a finite subset of $G$, and
  $support(q_{g₁, g₂}) ⊆ G''$ for all $g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\}$.
  Then for all $g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\}$,
  $sPoly(g₁, g₂) = ∑ g ∈ G'', q_{g₁, g₂}(g) * g$. -/
  let G'' : Finset G := G' ∪
    (G'.filter degFgEqA).attach.biUnion fun b₁ ↦
      (G'.filter degFgEqA).attach.biUnion fun b₂ ↦ (q b₁ b₂).support
  conv at hq =>
    ext g₁ g₂
    simp only [Finsupp.linearCombination_apply_of_mem_supported
        (l := (q g₁ g₂)) (s := G'')
        (hs := by
          simp? [Finsupp.mem_supported, G''] says
            simp only [Finset.coe_union, Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ,
              Set.iUnion_true, Finsupp.mem_supported, G'']
          apply Set.subset_union_of_subset_right
          exact Set.subset_iUnion₂_of_subset g₁ g₂ subset_rfl), smul_eq_mul]
  /- Substituting them into our decomposition by S-polynomials, we have:
  $$∑ g ∈ G' with (degree(f(g) * g) = a), leadingTerm(f(g)) * g
    = ∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
        c(g₁, g₂) * (lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * sPoly(g₁, g₂)
    = ∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
        c(g₁, g₂)•(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) *
        ∑ g ∈ G'', q_{g₁, g₂}(g) * g
    = ∑ g ∈ G'',
        (∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
          c(g₁, g₂)•(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * q_{g₁, g₂}(g)) *
        g. $$ (`h_sum_sPoly`)
  Note: degrees of $(f(g) - lt'(g)) * g$ and
    $c(g₁, g₂)•(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * q_{g₁, g₂} * g$ are
    both less than $a$. It is a key to complete the proof. We will proof it at the end. -/
  simp_rw [(hq _ _).1] at h_sum_sPoly
  replace hq (g₁ g₂ : G'.filter degFgEqA) := (hq g₁ g₂).2
  clear hsPoly -- clear the infoview (optional)
  simp_rw [mul_one, G''.mul_sum, ← mul_assoc, Finset.smul_sum,
    ← smul_mul_assoc, smul_monomial, Finset.sum_comm (t:=G''), ← Finset.sum_mul,
    smul_eq_mul (α := R)] at h_sum_sPoly
  /- With the assumption that $f(g)$ vanishes when $g ∉ G'$ and $G' ⊆ G''$, we have
  $$p = ∑ g ∈ G' with (degree(f(g) * g) = a), leadingTerm(f(g)) * g + ∑ g ∈ G', (f(g) - lt'(g)) * g
    = ∑ g ∈ G' with (degree(f(g) * g) = a), leadingTerm(f(g)) * g + ∑ g ∈ G'', (f(g) - lt'(g)) * g
    = ∑ g ∈ G'',
        (∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
           c(g₁, g₂)•(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * q_{g₁, g₂}(g)) *
        g +
      ∑ g ∈ G'', (f(g) - lt'(g)) * g
    = ∑ g ∈ G'',
        (∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
           c(g₁, g₂)•(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * q_{g₁, g₂}(g) +
         (f(g) - lt'(g))) *
        g.$$ -/
  convert_to p = _ + ∑ g ∈ G'', (f g - lt' g) * g using 2 at hp
  · exact Finset.sum_subset (by simp [G'']) (by simp_intro .. [hf₀support, lt'])
  simp_rw [h_sum_sPoly, ← Finset.sum_add_distrib, ← add_mul] at hp
  let f' : G → MvPolynomial σ R := fun x ↦
    (∑ x₁ : ↥(G'.filter degFgEqA), ∑ x₂ : ↥(G'.filter degFgEqA),
      monomial
          ((m.degree (f x₁.val) + m.degree (x₁.val : MvPolynomial σ R)) ⊔
              (m.degree (f x₂.val) + m.degree (x₂.val : MvPolynomial σ R)) -
            (m.degree (x₁.val : MvPolynomial σ R) ⊔
              m.degree (x₂.val : MvPolynomial σ R)))
        (c x₁.val x₂.val * 1) * q x₁ x₂ x) +
      (f x - lt' x)
  have hp' : p = ∑ x ∈ G'', f' x * x.val := by
    simpa only [f'] using hp
  /- Let $f'(g)$ be
  $$∑ g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\},
      c(g₁, g₂)•(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * q_{g₁, g₂}(g)
    + (f(g) - lt'(g)),$$
  and $a'$ be $max(degree(p), max_{g ∈ G''} degree(f'(g) * g))$. Then we have $p = ∑ g ∈ G'', f'(g) * g$,
  and apparently $degree(p) ≤ a'$ and $∀ g ∈ G'', degree(f'(g) * g) ≤ a'$. Now both
  $degree(p) ≤ a'$ and $P(a')$ are got.
  To prove the theorem, it remains to prove that $a' < a$. -/
  refine ⟨m.toSyn (m.degree p) ⊔ G''.sup fun g ↦ m.toSyn <| m.degree <| f' g * g.val,
    (?_ : _ < _), by simp, f', G'', hp', ?le_max⟩
  case le_max =>
    intro h g
    rw [mul_comm]
    exact le_trans (Finset.le_sup (f := fun g ↦ m.toSyn <| m.degree (f' g * g.val)) g)
      le_sup_right
  /- It suffices that $degree(f'(g) * g) < a$ for all $g ∈ G''$. Then it suffices that, degrees of
  the left side (too long...) and the right side $f(g) - lt'(g)$ of the outermost $+$ in $f'$
  multiplied by $g$ respectively are both less than $a$ for all $g ∈ G''$.
  -/
  clear hp h_sum_sPoly -- remove them since they're long and will not be used anymore
  simp only [max_lt_iff, ha, Finset.sup_lt_iff h_a_gt_zero, true_and]
  intro g hg'
  simp only [f', add_mul]
  apply lt_of_le_of_lt degree_add_le
  apply max_lt
  · /- To prove the left side, it suffices to show
    $degree(c(g₁, g₂)•(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) *
      q_{g₁, g₂}(g) * g) < a$
    for all $g₁, g₂ ∈ \{g ∈ G' | degree(f(g) * g) = a\}$ (`g₁`, `g₂`). -/
    simp_rw [Finset.sum_mul]
    refine lt_of_le_of_lt m.degree_sum_le <| (Finset.sup_lt_iff h_a_gt_zero).mpr ?_
    simp only [Finset.mem_univ, forall_const]
    intro g₁
    refine lt_of_le_of_lt m.degree_sum_le <| (Finset.sup_lt_iff h_a_gt_zero).mpr ?_
    simp only [Finset.mem_univ, forall_const]
    intro g₂
    /- We may assume $q_{g₁, g₂}(g) ≠ 0$; otherwise this summand is zero.
    The standard-representation hypothesis then bounds the degree of its product with $g$.
    $$degree(
      c(g₁, g₂) • (lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)) / lcm(lm(g₁), lm(g₂))) * q_{g₁, g₂}(g) * g)
    ≤ degree(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂))) - degree(lcm(lm(g₁), lm(g₂))) +
        degree(q_{g₁, g₂}(g) * g)$$ -/
    by_cases hq0 : (q g₁ g₂) g = 0
    · simp [hq0, h_a_gt_zero]
    have h_deg_gq_lt_sup := hq g₁ g₂ g hq0
    rw [mul_assoc]
    apply lt_of_le_of_lt degree_mul_le
    rw [AddEquiv.map_add]
    refine add_lt_of_add_lt_right ?_ (degree_monomial_le _)
    /- $$... < degree(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂))) - degree(lcm(lm(g₁), lm(g₂))) +
                degree(lcm(lm(g₁), lm(g₂)))$$ -/
    apply lt_of_lt_of_le (add_lt_add_right
      (mul_comm g.val (q _ _ g) ▸ h_deg_gq_lt_sup) _)
    /- $$... = degree(lcm(lm(f(g₁) * g₁), lm(f(g₂) * g₂)))$$ -/
    rw [← AddEquiv.map_add, tsub_add_cancel_of_le <| sup_le_sup (by simp) (by simp)]
    /- $$... ≤ a.$$ -/
    have hfgg₁ := (G'.mem_filter.mp g₁.2).2
    have hfgg₂ := (G'.mem_filter.mp g₂.2).2
    unfold degFgEqA at hfgg₁ hfgg₂
    rw [degree_mul_of_right_mem_nonZeroDivisors _ hG₀, ← m.toSyn.eq_symm_apply] at hfgg₁ hfgg₂
    · simp [hfgg₁, hfgg₂]
    all_goals
      by_contra! hfg0
      simp [hfg0, h_a_gt_zero.ne] at hfgg₁ hfgg₂
  · /- It remains to prove $degree((f(g) - lt'(g)) * g) < a$. -/
    wlog h : degFgEqA g
    · by_cases hg'G' : g ∈ G'
      · simp [h, lt', lt_of_le_of_ne (mul_comm (f g) g ▸ h_deg_le g hg'G') h]
      · simp [hg'G', h_a_gt_zero, lt', hf₀support]
    simp? [h, lt'] says simp only [h, ↓reduceIte, lt']
    wlog! +distrib hLTgg' : f g - m.leadingTerm (f g) ≠ 0
    · simp [hLTgg', h_a_gt_zero]
    rw [← h] at ⊢ h_a_gt_zero
    apply ne_of_lt at h_a_gt_zero
    rw [ne_eq, eq_comm, toSyn_eq_zero_iff] at h_a_gt_zero
    have : f g ≠ 0 := by
      have := m.ne_zero_of_degree_ne_zero h_a_gt_zero
      contrapose! this
      simp [this]
    simp [degree_mul_of_right_mem_nonZeroDivisors hLTgg' hG₀,
      degree_mul_of_right_mem_nonZeroDivisors this hG₀,
      m.degree_sub_leadingTerm_lt_degree (m.degree_ne_zero_of_sub_leadingTerm_ne_zero hLTgg')]

end CommRing

end IsGroebnerBasis

end MonomialOrder
