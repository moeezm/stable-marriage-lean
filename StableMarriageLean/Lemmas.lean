import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Erase
import StableMarriageLean.GaleShapley

namespace StableMarriageLean

noncomputable section
open Classical
open Mathlib

-- utils
lemma prefersOpt_false_on_equal_inputs (p : Preferences Agent Partner)
  (a : Agent) (x : Option Partner) : prefersOpt p a x x = False := by
  unfold prefersOpt
  cases x with
  | some y =>
    simp
    by_cases acceptable : p.acceptable a y
    ·
      simp [acceptable]
      simp [p.prefers_irrefl]
    ·
      grind
  | none =>
    grind

-- Strict preferences are asymmetric.
lemma prefers_asymm {Agent Partner : Type*} (p : Preferences Agent Partner)
    (a : Agent) (o1 o2 : Partner) :
    p.prefers a o1 o2 → ¬ p.prefers a o2 o1 := by
  intro h12 h21
  have h := p.prefers_trans a o1 o2 o1 h12 h21
  exact (p.prefers_irrefl a o1) h

-- PrefersOpt is asymmetric on explicit options.
lemma prefersOpt_asymm {Agent Partner : Type*} (p : Preferences Agent Partner)
    (a : Agent) (o1 o2 : Partner) :
    prefersOpt p a (some o1) (some o2) → ¬ prefersOpt p a (some o2) (some o1) := by
  intro h12 h21
  by_cases hacc1 : p.acceptable a o1
  · by_cases hacc2 : p.acceptable a o2
    · have h12' : p.prefers a o1 o2 := by
        simpa [prefersOpt, hacc1, hacc2] using h12
      have h21' : p.prefers a o2 o1 := by
        simpa [prefersOpt, hacc2, hacc1] using h21
      exact (prefers_asymm p a o1 o2 h12') h21'
    ·
      simp [prefersOpt, hacc2] at h21
  ·
    simp [prefersOpt, hacc1] at h12

lemma prefersOpt_irrefl_for_explicit (p : Preferences Agent Partner)
  (a : Agent) (o : Partner) : ¬ prefersOpt p a (some o) (some o) := by
  unfold prefersOpt
  simp
  intro h
  split_ands
  ·
    exact h
  ·
    exact p.prefers_irrefl a o

lemma prefersOpt_trans (p : Preferences Agent Partner)
  (a : Agent) (o1 o2 o3 : Option Partner) :
  prefersOpt p a o1 o2 ∧ prefersOpt p a o2 o3 → prefersOpt p a o1 o3 := by
  unfold prefersOpt
  intro ⟨h1, h2⟩
  cases o1 <;> cases o2 <;> cases o3 <;> simp at h1 h2 <;> simp_all
  rename_i x1 x2 x3
  intro x3_acceptable
  have x1_over_x2 := h1.right
  have x2_over_x3 := h2.right x3_acceptable
  exact p.prefers_trans a x1 x2 x3 x1_over_x2 x2_over_x3

lemma chooseMaxCandidate_is_best (σ : GSState P) (m : P.Men)
  (h : (candidateWomen P σ m).Nonempty) :
  woman_is_better_than_all_candidates σ m (chooseMaxCandidate P σ m h) := by
  set w := chooseMaxCandidate P σ m h with w_eq
  have w_acceptable : P.menPrefs.acceptable m w := by
    exact chooseMaxCandidate_is_acceptable σ m h
  unfold woman_is_better_than_all_candidates
  intro w' h_w'_candidate w'_neq_w
  unfold prefersOpt
  simp
  split_ands
  · -- prove acceptable
    exact chooseMaxCandidate_is_acceptable σ m h
  · -- prove better
    intro w'_acceptable
    have not_prefers := chooseMaxCandidate_no_better P σ m h w' h_w'_candidate
    rw [← w_eq] at not_prefers
    have total := P.menPrefs.prefers_total m w w' w_acceptable w'_acceptable
    grind

-- consistency
lemma galeShapley_initial_consistent (P : Problem) : consistent P (GSState.initial P).matching := by
  unfold GSState.initial consistent
  simp
lemma galeShapley_stepWith_preserves_consistency (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
(h_mfree : isFree P σ m) (h_consistent : consistent P σ.matching)
: consistent P (GSState.stepWith P σ m w).matching := by
  unfold consistent at h_consistent ⊢
  unfold isFree at h_mfree
  unfold GSState.stepWith
  simp
  split <;> split <;> simp
  unfold Matching.matchUnmatched
  simp
  grind
  grind
  unfold Matching.swapMatch
  simp
  intro m' w'
  by_cases w'_eq_w : w' = w
  case pos =>
    grind
  case neg =>
    simp [w'_eq_w]
    rename_i w_old_match is_old_match prefers_m
    constructor
    case mp =>
      intro h
      grind
    case mpr =>
      intro h
      have m'_matched_to_w' : σ.matching.menMatches m' = (some w') := by
        grind
      have m'_neq_m : m' ≠ m := by
        grind
      have w_old_match_matched_to_w' : σ.matching.menMatches w_old_match = (some w) := by
        grind
      have m'_neq_w_old_match : m' ≠ w_old_match := by
        grind
      grind
  grind
lemma galeShapley_step_preserves_consistency (P: Problem) (σ : GSState P) (h_consistent : consistent P σ.matching)
: consistent P (GSState.step P σ).matching := by
  unfold GSState.step
  split
  case isTrue hfree =>
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    show consistent P (GSState.stepWith P σ m w).matching
    exact galeShapley_stepWith_preserves_consistency P σ m w hm h_consistent
  case isFalse =>
    exact h_consistent
lemma galeShapley_n_steps_preserves_consistency (P : Problem) (n : Nat) : consistent P (GSState.runSteps P n).matching := by
  induction n with
  | zero =>
    unfold GSState.runSteps
    exact galeShapley_initial_consistent P
  | succ n ih =>
    unfold GSState.runSteps
    exact galeShapley_step_preserves_consistency P (GSState.runSteps P n) ih


-- individual rationality
lemma galeShapley_initial_individually_rational (P : Problem) : individuallyRational P (GSState.initial P).matching := by
  unfold individuallyRational GSState.initial
  simp

lemma galeShapley_stepWith_preserves_individual_rationality (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
(h_rational : individuallyRational P σ.matching) (h_acceptable : P.menPrefs.acceptable m w):
  individuallyRational P (GSState.stepWith P σ m w).matching := by
  unfold individuallyRational
  unfold individuallyRational at h_rational
  unfold GSState.stepWith
  split <;> split <;> simp
  unfold Matching.matchUnmatched
  simp
  rename_i prefers_m old_match_none
  unfold prefersOpt at old_match_none
  simp at old_match_none
  grind
  grind
  rename_i old_match old_match_some prefers_m
  unfold Matching.swapMatch
  simp
  unfold prefersOpt at prefers_m
  simp at prefers_m
  grind
  grind

lemma galeShapley_step_preserves_individual_rationality (P : Problem) (σ : GSState P) (h_rational : individuallyRational P σ.matching)
: individuallyRational P (GSState.step P σ).matching := by
  unfold GSState.step
  simp
  split_ifs
  case pos hfree =>
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    show individuallyRational P (GSState.stepWith P σ m w).matching
    have w_acceptable := chooseMaxCandidate_is_acceptable σ m hm.2
    exact galeShapley_stepWith_preserves_individual_rationality P σ m w h_rational w_acceptable
  case neg =>
    exact h_rational

lemma galeShaley_n_steps_preserves_individual_rationality (P : Problem) (n : Nat)
: individuallyRational P (GSState.runSteps P n).matching := by
  induction n with
  | zero =>
    unfold GSState.runSteps
    exact galeShapley_initial_individually_rational P
  | succ n ih =>
    unfold GSState.runSteps
    exact galeShapley_step_preserves_individual_rationality P (GSState.runSteps P n) ih

-- termination
-- general idea: termination means there are no free men
-- "clearly", sum of proposals length is bounded by n * m (proposalBound)
-- somewhat less clearly, if sum of proposals length is n * m, then each proposal list is full so no man is free
-- there is a free man iff GSState.step calls GSState.stepWith which will always increase the sum of proposal lengths by 1
-- by induction we can prove that GSState.runSteps K is either terminated or sum of proposal lengths is K
def proposal_length (σ : GSState P) (m : P.Men) := (σ.men_proposals m).card
def proposal_count (σ : GSState P) : Nat := Finset.sum (P.menFintype.elems) (proposal_length σ)
def m_card (P : Problem) : Nat :=
  letI := P.menFintype
  Fintype.card P.Men
def w_card (P : Problem) : Nat :=
  letI := P.womenFintype
  Fintype.card P.Women
lemma man_proposals_le_num_of_women (σ : GSState P) (m : P.Men) :
  proposal_length σ m ≤ (w_card P) := by
    letI := P.womenFintype
    unfold proposal_length
    exact Finset.card_le_univ (σ.men_proposals m)
lemma proposal_count_le_proposalBound (σ : GSState P) : proposal_count σ ≤ proposalBound P := by
  unfold proposalBound proposal_count
  have function_ver : ∀ m ∈ P.menFintype.elems, proposal_length σ m ≤ ((fun _ => w_card P) m) := by
    simp
    intro m h
    exact man_proposals_le_num_of_women σ m
  calc
    Finset.sum (P.menFintype.elems) (proposal_length σ) ≤ Finset.sum (P.menFintype.elems) (fun _ => w_card P) := by
      exact Finset.sum_le_sum function_ver
    _ ≤ m_card P * w_card P:= by
      simp
      exact Nat.le_refl (m_card P * w_card P)
lemma m_not_free_if_proposal_length_eq_num_of_women (σ : GSState P) (m : P.Men) (h_full : proposal_length σ m = w_card P)
: ¬ isFree P σ m := by
  unfold isFree
  unfold candidateWomen
  letI := P.womenFintype
  have stupid : w_card P = P.womenFintype.elems.card := by
    unfold w_card
    exact rfl
  have finset_card_eq : proposal_length σ m = P.womenFintype.elems.card := by
    omega
  have finset_subset : σ.men_proposals m ⊆ P.womenFintype.elems := by
    intro x hx
    exact Fintype.complete x
  have finset_eq : σ.men_proposals m = P.womenFintype.elems := by
    unfold proposal_length at finset_card_eq
    simp [Finset.eq_of_superset_of_card_ge finset_subset (by omega)]
  have all_women_proposed : ∀ w : P.Women, w ∈ σ.men_proposals m := by
    intro w
    have w_in_finset : w ∈ P.womenFintype.elems := by
      exact Fintype.complete w
    grind
  grind
lemma all_m_proposal_length_maxed_if_proposal_count_eq_proposalBound (σ : GSState P) : proposal_count σ = proposalBound P →
(∀ m : P.Men, proposal_length σ m = w_card P) := by
  intro h
  unfold proposalBound at h
  letI := P.menFintype
  have function_ver : ∀ m ∈ P.menFintype.elems, proposal_length σ m ≤ ((fun _ => w_card P) m) := by
    simp
    intro m h
    exact man_proposals_le_num_of_women σ m
  have thing := (Finset.sum_eq_sum_iff_of_le function_ver).mp (by aesop)
  intro m
  have m_in_elems : m ∈ P.menFintype.elems := by exact Fintype.complete m
  exact thing m m_in_elems

lemma all_m_not_free_if_proposal_count_eq_proposalBound (σ : GSState P) : proposal_count σ = proposalBound P →
(∀ m : P.Men, ¬ isFree P σ m) := by
  intro h
  have maxed := all_m_proposal_length_maxed_if_proposal_count_eq_proposalBound σ h
  intro m
  specialize maxed m
  exact m_not_free_if_proposal_length_eq_num_of_women σ m maxed

lemma terminated_if_proposal_count_eq_proposalBound (σ : GSState P) : proposal_count σ = proposalBound P →
terminated P σ := by
  intro h
  unfold terminated
  simp
  exact fun x => all_m_not_free_if_proposal_count_eq_proposalBound σ h x

lemma galeShapley_stepWith_increase_proposal_count (σ : GSState P) (m : P.Men) (w : P.Women) (h_not_proposed : w ∉ σ.men_proposals m):
proposal_count (GSState.stepWith P σ m w) = proposal_count σ + 1 := by
  set new_state := GSState.stepWith P σ m w with new_state_eq
  letI := P.menFintype
  have neq_m_equal_length (m' : P.Men) (h_neq : m' ≠ m) : proposal_length new_state m' = proposal_length σ m' := by
    unfold proposal_length new_state GSState.stepWith
    have stupid : ¬ m = m' := by grind
    split <;> split <;> simp <;> simp [stupid]
  have m_length_plus_one : proposal_length new_state m = (proposal_length σ m) + 1 := by
    unfold proposal_length new_state GSState.stepWith
    simp
    split <;> split <;> simp <;> exact Finset.card_insert_of_notMem h_not_proposed
  have stupid : m ∈ P.menFintype.elems := by exact Fintype.complete m
  have split_sum_old := Finset.sum_erase_add P.menFintype.elems (proposal_length σ) stupid
  have split_sum_new := Finset.sum_erase_add P.menFintype.elems (proposal_length new_state) stupid
  have erase_m_equal_length : ∀ m' ∈ P.menFintype.elems.erase m, proposal_length new_state m' = proposal_length σ m' := by
    intro m' h_notin
    have m'_neq_m : m' ≠ m := by exact Finset.ne_of_mem_erase h_notin
    grind
  simp [m_length_plus_one] at split_sum_new
  unfold proposal_count
  calc
    _ = ∑ x ∈ Fintype.elems.erase m, proposal_length new_state x + (proposal_length σ m + 1) := by exact id (Eq.symm split_sum_new)
    _ = (∑ x ∈ Fintype.elems.erase m, proposal_length new_state x + proposal_length σ m) + 1 := by omega
    _ = (∑ x ∈ Fintype.elems.erase m, proposal_length σ x + proposal_length σ m) + 1 := by
      have sum_parts_eq := Finset.sum_congr (s₁ := P.menFintype.elems.erase m) (s₂ := P.menFintype.elems.erase m) (by rfl) erase_m_equal_length
      grind
    _ = _ := by
      grind

lemma galeShapley_step_on_terminated_is_terminated (σ : GSState P) (h_terminated : terminated P σ)
: terminated P (GSState.step P σ) := by
  unfold terminated at h_terminated ⊢
  unfold GSState.step
  grind

lemma galeShapley_n_steps_is_terminated_or_proposal_count_is_n (P : Problem) (n : Nat) :
(terminated P (GSState.runSteps P n)) ∨ (proposal_count (GSState.runSteps P n) = n) := by
  induction n with
  | zero =>
    right
    unfold proposal_count proposal_length GSState.runSteps GSState.initial
    simp
  | succ k ih =>
    cases ih with
    | inl h_terminated =>
      left
      unfold GSState.runSteps
      exact galeShapley_step_on_terminated_is_terminated (GSState.runSteps P k) h_terminated
    | inr h_count =>
      unfold GSState.runSteps GSState.step
      split_ifs
      case pos h_free =>
        right
        set σ := (GSState.runSteps P k) with σ_eq
        let m := Classical.choose h_free
        have hm : isFree P σ m := Classical.choose_spec h_free
        let w := chooseMaxCandidate P σ m hm.2
        have w_candidate : w ∈ candidateWomen P σ m := by exact chooseMaxCandidate_mem P σ m hm.right
        have w_notproposed : w ∉ σ.men_proposals m := by
          unfold candidateWomen at w_candidate
          grind
        show proposal_count (GSState.stepWith P σ m w) = k + 1
        rw [← h_count]
        exact galeShapley_stepWith_increase_proposal_count σ m w w_notproposed
      case neg h_notfree =>
        left
        unfold terminated
        grind

-- no blocking pairs
lemma galeShapley_initial_state_satisfies_invariants (P : Problem):
  state_satisfies_invariants (GSState.initial P) := by
  unfold GSState.initial
  unfold state_satisfies_invariants
  unfold man_prefers_final_match_to_all_non_proposees
  unfold woman_prefers_final_match_to_all_suitors
  split_ands
  · -- man invariants
    intro m partner p
    simp [partner]
  · -- woman invariants
    intro w partner m h
    aesop

lemma galeShapley_stepWith_woman_better_than_all_candidates_preserves_invariants (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
(h_wbetter : woman_is_better_than_all_candidates σ m w) (h_wcandidate : w ∈ candidateWomen P σ m)
(h_rational : individuallyRational P σ.matching) :
  state_satisfies_invariants σ → state_satisfies_invariants (GSState.stepWith P σ m w) := by
  intro h
  have h2 := h
  unfold state_satisfies_invariants man_prefers_final_match_to_all_non_proposees woman_prefers_final_match_to_all_suitors at h2
  set new_state := GSState.stepWith P σ m w with new_state_eq
  have not_m_not_w_match_matching_unaffected : ∀ m' ≠ m, σ.matching.womenMatches w ≠ (some m') →
    new_state.matching.menMatches m' = σ.matching.menMatches m' := by
    intro m' m'_neq_m m'_not_w_match
    unfold new_state GSState.stepWith
    simp
    unfold Matching.matchUnmatched Matching.swapMatch
    split <;> split <;> simp <;> grind
  have not_m_proposals_unaffected : ∀ m' ≠ m, new_state.men_proposals m' = σ.men_proposals m' := by
    unfold new_state GSState.stepWith
    intro m' m'_neq_m
    split <;> split <;> grind
  have m_proposals_change_is_just_w : new_state.men_proposals m = {w} ∪ (σ.men_proposals m) := by
    unfold new_state GSState.stepWith
    aesop
  have not_w_matching_unaffected : ∀ w' ≠ w, new_state.matching.womenMatches w' = σ.matching.womenMatches w' := by
    unfold new_state GSState.stepWith
    intro w' w'_new_w
    simp
    unfold Matching.matchUnmatched Matching.swapMatch
    split <;> split <;> simp <;> grind
  have not_w_proposals_unaffected : ∀ w' ≠ w, ∀ m : P.Men, w' ∈ new_state.men_proposals m ↔ w' ∈ σ.men_proposals m := by
    intro w' h_neq m'
    by_cases m_eq_m' : m = m'
    · -- equal
      rw [← m_eq_m']
      grind
    · -- not equal
      specialize not_m_proposals_unaffected m' (by grind)
      rw [not_m_proposals_unaffected]
  have man_not_m_not_w_match_still_valid : ∀ m' ≠ m, σ.matching.womenMatches w ≠ (some m') →
    man_prefers_final_match_to_all_non_proposees new_state m' := by
      intro m' h_notm h_notwmatch
      unfold man_prefers_final_match_to_all_non_proposees
      specialize not_m_proposals_unaffected m' h_notm
      specialize not_m_not_w_match_matching_unaffected m' h_notm h_notwmatch
      grind
  have woman_not_w_still_valid : ∀ w' ≠ w, woman_prefers_final_match_to_all_suitors new_state w' := by
    intro w' h_neq
    unfold woman_prefers_final_match_to_all_suitors
    specialize not_w_matching_unaffected w' h_neq
    simp [not_w_matching_unaffected]
    intro m'
    simp [not_w_proposals_unaffected w' h_neq]
    have women_invariant := h.right
    specialize women_invariant w' m'
    grind
  have new_non_proposee_of_man_is_old_non_proposee : ∀ m' : P.Men, ∀ w' ∉ new_state.men_proposals m', w' ∉ σ.men_proposals m' := by
    intro m'
    by_cases m'_is_m : m' = m <;> grind
  have new_suitor_of_w_is_m_or_old_suitor : ∀ m', w ∈ new_state.men_proposals m' → (m' = m ∨ w ∈ σ.men_proposals m') := by
    grind
  -- easy unchanged cases done
  -- proof for m
  have m_match_either_old_or_w : (new_state.matching.menMatches m = σ.matching.menMatches m) ∨
  (new_state.matching.menMatches m = some w) := by
    unfold new_state
    unfold GSState.stepWith
    simp
    unfold Matching.matchUnmatched Matching.swapMatch
    split <;> split <;> simp
    rename_i w_prefers
    rename_i h_wmatch
    rename_i w_match
    have thing := prefersOpt_irrefl_for_explicit P.womenPrefs w m
    have w_match_neq_m : w_match ≠ m := by
      grind
    grind
  have m_valid : man_prefers_final_match_to_all_non_proposees new_state m := by
    unfold man_prefers_final_match_to_all_non_proposees
    cases m_match_either_old_or_w with
    | inl h_oldmatch =>
      simp [h_oldmatch]
      cases h_m_match_is_none : σ.matching.menMatches m with
      | none =>
        simp
      | some old_partner =>
        simp
        intro w' h_not_proposed_new
        have h_not_proposed_old := new_non_proposee_of_man_is_old_non_proposee m w' h_not_proposed_new
        have invariant := h2.left m
        simp [h_m_match_is_none] at invariant
        grind
    | inr h_wmatch =>
      simp [h_wmatch]
      intro w' h_not_proposed_new
      have h_not_proposed_old := new_non_proposee_of_man_is_old_non_proposee m w' h_not_proposed_new
      by_cases w'_acceptable : P.menPrefs.acceptable m w'
      · -- acceptable
        have w'_candidate : w' ∈ candidateWomen P σ m := by
          unfold candidateWomen
          grind
        unfold woman_is_better_than_all_candidates at h_wbetter
        specialize h_wbetter w'
        grind
      · -- not acceptable
        have w_acceptable : P.menPrefs.acceptable m w := by
          unfold candidateWomen at h_wcandidate
          grind
        unfold prefersOpt
        simp
        grind
  -- proof for w's old match
  let w_match_prop : Prop :=
    match σ.matching.womenMatches w with
    | none => True
    | some w_old_partner => man_prefers_final_match_to_all_non_proposees new_state w_old_partner
  have w_match_valid : w_match_prop := by
    unfold w_match_prop
    cases h_w_had_match : σ.matching.womenMatches w with
    | none => simp
    | some w_old_partner =>
      simp
      unfold man_prefers_final_match_to_all_non_proposees
      simp
      have w_old_partner_partner_is_unchanged_or_none :
      (new_state.matching.menMatches w_old_partner = σ.matching.menMatches w_old_partner) ∨
      (new_state.matching.menMatches w_old_partner = none) := by
        unfold new_state GSState.stepWith
        simp
        unfold Matching.matchUnmatched Matching.swapMatch
        split <;> split <;> simp <;> grind
      cases w_old_partner_partner_is_unchanged_or_none with
      | inl w_old_partner_is_unchanged =>
        simp [w_old_partner_is_unchanged]
        cases w_old_partner_old_partner_is_some :  σ.matching.menMatches w_old_partner with
        | none => simp
        | some w_old_partner_old_partner =>
          simp
          intro w' h_not_proposed_new
          have h_not_proposed_old := new_non_proposee_of_man_is_old_non_proposee w_old_partner w' h_not_proposed_new
          have invariant := h2.left w_old_partner
          simp at invariant
          grind
      | inr w_old_partner_is_none =>
        grind

  -- proof for w
  have w_old_match_acceptable (old_match : P.Men) (is_old_match : σ.matching.womenMatches w = (some old_match)) :
  P.womenPrefs.acceptable w old_match := by
    unfold individuallyRational at h_rational
    grind
  have w_valid : woman_prefers_final_match_to_all_suitors new_state w := by
    unfold woman_prefers_final_match_to_all_suitors
    simp
    intro suitor is_suitor
    unfold new_state GSState.stepWith Matching.matchUnmatched Matching.swapMatch
    have invariant := h2.right w
    simp at invariant
    split <;> split <;> simp
    case h_1.isTrue w_old_partner_is_none w_prefers_m =>
      -- w was matched to none previously and prefers m to none
      by_cases m_is_suitor : m = suitor <;> simp [m_is_suitor]
      case neg =>
        have suitor_is_old : new_state.men_proposals suitor = σ.men_proposals suitor := by
          grind
        simp [suitor_is_old] at is_suitor
        specialize invariant suitor is_suitor
        cases invariant with
        | inl stupid => grind
        | inr prefers_match_to_suitor =>
          simp [w_old_partner_is_none] at prefers_match_to_suitor
          exact prefersOpt_acceptable_over_unacceptable P.womenPrefs w m suitor w_prefers_m prefers_match_to_suitor
    case h_1.isFalse w_old_partner_is_none w_not_prefers_m =>
      -- w was matched to none previously and doesn't prefer m to none
      rw [w_old_partner_is_none]
      simp
      /-
      goal state looks a bit odd (practically, show none > (some suitor)) but the key
      is actually w_not_prefers_m so we can use the invariant
      -/
      by_cases m_is_suitor : m = suitor
      case pos =>
        unfold prefersOpt at w_not_prefers_m
        simp at w_not_prefers_m
        unfold prefersOpt
        grind
      case neg =>
        have suitor_is_old : new_state.men_proposals suitor = σ.men_proposals suitor := by
          grind
        simp [suitor_is_old] at is_suitor
        specialize invariant suitor is_suitor
        grind
    case h_2.isTrue w_old_partner w_old_partner_is_some w_prefers_m =>
      -- w had a previous partner and prefers m to him
      by_cases m_is_suitor : m = suitor
      case pos =>
        grind
      case neg =>
        simp [m_is_suitor]
        have suitor_is_old_proposer : w ∈ σ.men_proposals suitor := by
          grind
        by_cases old_partner_is_suitor : w_old_partner = suitor
        case pos =>
          grind
        case neg =>
          have thing : prefersOpt P.womenPrefs w (some w_old_partner) (some suitor) := by
            specialize invariant suitor
            grind
          exact prefersOpt_trans P.womenPrefs w m w_old_partner suitor ⟨w_prefers_m, thing⟩
    case h_2.isFalse w_old_partner w_old_partner_is_some w_not_prefers_m =>
      -- w had a previous partner and doesn't prefer m to him
      -- should be practically the same as h_1.isFalse above, since it's really about the invariant
      simp [w_old_partner_is_some]
      by_cases m_is_suitor : m = suitor
      case pos =>
        rw [← m_is_suitor]
        unfold prefersOpt at w_not_prefers_m
        simp at w_not_prefers_m
        unfold prefersOpt
        simp
        by_cases m_acceptable : P.womenPrefs.acceptable w m
        case pos =>
          simp [m_acceptable] at w_not_prefers_m
          have prefers_old_partner_or_m := P.womenPrefs.prefers_total w m w_old_partner m_acceptable w_not_prefers_m.left
          grind
        case neg =>
          grind
      case neg =>
        have suitor_is_old : new_state.men_proposals suitor = σ.men_proposals suitor := by
          grind
        simp [suitor_is_old] at is_suitor
        specialize invariant suitor is_suitor
        grind
  -- finish up
  unfold state_satisfies_invariants
  split_ands
  · -- men
    intro m'
    by_cases h_is_m : m' = m <;> grind
  · -- women
    intro w'
    grind

lemma galeShapley_step_preserves_invariants (P : Problem) (σ : GSState P) (h_rational : individuallyRational P σ.matching):
  state_satisfies_invariants σ → state_satisfies_invariants (σ.step P) := by
  intro h
  unfold GSState.step
  by_cases hfree : ∃ m, isFree P σ m <;> simp [hfree]
  · -- free man exists, do step
    set m := Classical.choose hfree
    have hm_spec : isFree P σ m := Classical.choose_spec hfree
    set w := chooseMaxCandidate P σ m hm_spec.2
    show state_satisfies_invariants (GSState.stepWith P σ m w)
    have w_better : woman_is_better_than_all_candidates σ m w := by
      apply chooseMaxCandidate_is_best
    have w_candidate : w ∈ candidateWomen P σ m := by
      exact chooseMaxCandidate_mem P σ m hm_spec.right
    exact
      galeShapley_stepWith_woman_better_than_all_candidates_preserves_invariants P σ m w
        w_better w_candidate h_rational h
  · -- no free man, no step, use hypothesis
    exact h

lemma galeShapley_n_steps_satisfies_invariants (P : Problem) (n : Nat) :
  state_satisfies_invariants (GSState.runSteps P n) := by
  have stronger : state_satisfies_invariants (GSState.runSteps P n) ∧ individuallyRational P (GSState.runSteps P n).matching := by
    induction n with
    | zero =>
      unfold GSState.runSteps
      exact ⟨galeShapley_initial_state_satisfies_invariants P, galeShapley_initial_individually_rational P⟩
    | succ n ih =>
      unfold GSState.runSteps
      have invariant := galeShapley_step_preserves_invariants P (GSState.runSteps P n) ih.right ih.left
      have rational := galeShapley_step_preserves_individual_rationality P (GSState.runSteps P n) ih.right
      exact ⟨invariant, rational⟩
  exact stronger.left

end

end StableMarriageLean
