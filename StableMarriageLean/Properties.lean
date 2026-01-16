import StableMarriageLean.GaleShapley
import StableMarriageLean.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase

namespace StableMarriageLean

noncomputable section
open Classical
open Mathlib

-- The output matching is consistent.
theorem galeShapley_consistent (P : Problem) :
    consistent P (galeShapley P) := by
  unfold galeShapley
  exact galeShapley_n_steps_preserves_consistency P (proposalBound P)

-- The algorithm terminates after the proposal bound.
theorem galeShapley_terminates (P : Problem) : terminated P (GSState.runSteps P (proposalBound P)) := by
  have choices := galeShapley_n_steps_is_terminated_or_proposal_count_is_n P (proposalBound P)
  cases choices with
  | inl h_terminated => trivial
  | inr h_full =>
    exact
      terminated_if_proposal_count_eq_proposalBound (GSState.runSteps P (proposalBound P)) h_full

-- The output matching is individually rational.
theorem galeShapley_individuallyRational (P : Problem) : individuallyRational P (galeShapley P) := by
  unfold galeShapley
  exact galeShaley_n_steps_preserves_individual_rationality P (proposalBound P)

-- There are no blocking pairs
theorem galeShapley_noBlockingPairs (P : Problem) :
    ∀ m w, ¬ blockingPair P (galeShapley P) m w := by
    intro m w hblock
    set σ := GSState.runSteps P (proposalBound P) with σ_eq
    have ret_is_sigma_matching : (galeShapley P) = σ.matching := by
      aesop
    rw [ret_is_sigma_matching] at hblock
    unfold blockingPair at hblock
    have ⟨man_invariants, woman_invariants⟩ : state_satisfies_invariants σ := by
      rw [σ_eq]
      exact galeShapley_n_steps_satisfies_invariants P (proposalBound P)
    by_cases man_proposed : w ∈ σ.men_proposals m
    · -- m proposed to w
      specialize woman_invariants w m man_proposed
      cases woman_invariants with
      | inl m_is_match =>
        /-
        here we have that m and w are matched so we want to use the irreflexivity of
        prefers to contract that w prefers m to her match (m)
        -/
        have w_prefers := hblock.right.right
        rw [m_is_match] at w_prefers
        have w_prefers_not := prefersOpt_false_on_equal_inputs P.womenPrefs w (some m)
        aesop
      | inr m_is_not_match =>
        /-
        Here m is not w's final match. We split on whether w's match is none or some m'.
        We can rule out the none case because m and w are an acceptable pair, so w cannot
        prefer none to m.
        We rule out the some m' case by antisymmetry
        -/
        cases matched_type : σ.matching.womenMatches w with
        | some m' =>
          rw [matched_type] at m_is_not_match hblock
          have preference := hblock.right.right
          have not_preference := prefersOpt_asymm P.womenPrefs w m' m m_is_not_match
          grind
        | none =>
          simp [matched_type] at m_is_not_match
          unfold prefersOpt at m_is_not_match
          simp at m_is_not_match
          -- m_is_not_match simplified to w and m are not acceptable so we contradict
          have acceptable_pair := hblock.left
          unfold Problem.acceptablePair at acceptable_pair
          grind
    · -- m did not propose to w
      specialize man_invariants m
      unfold man_prefers_final_match_to_all_non_proposees at man_invariants
      simp at man_invariants

      /-
      Same proof as the did not match case of above. We have that match > (some w)
      and (some w) > match. We case match on none or some w'. If none then impossible since
      m and w are acceptable. Otherwise we use antisymmetry
      -/
      cases matched_type : σ.matching.menMatches m with
      | some w' =>
        rw [matched_type] at man_invariants hblock
        have preference := hblock.right.left
        simp at man_invariants
        have not_preference := prefersOpt_asymm P.menPrefs m w' w (man_invariants w man_proposed)
        grind
      | none =>
        have w_acceptable : P.menPrefs.acceptable m w := by
          unfold Problem.acceptablePair at hblock
          grind
        have w_is_candidate : w ∈ (candidateWomen P σ m) := by
          unfold candidateWomen
          grind
        have candidate_nonempty : (candidateWomen P σ m).Nonempty := by grind
        have σ_terminated : terminated P σ := by
          exact galeShapley_terminates P
        unfold terminated at σ_terminated
        simp at σ_terminated
        specialize σ_terminated m
        unfold isFree at σ_terminated
        have m_match_not_none : σ.matching.menMatches m ≠ none := by
          grind
        grind

-- The output matching is stable.
theorem galeShapley_stable (P : Problem) : stable P (galeShapley P) := by
  classical
  refine ⟨galeShapley_consistent P, ?_, ?_⟩
  · exact galeShapley_individuallyRational P
  · intro m w
    exact galeShapley_noBlockingPairs P m w

end

end StableMarriageLean
