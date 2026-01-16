import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Preorder.Finite
import StableMarriageLean.Basic

namespace StableMarriageLean

noncomputable section
open Classical

-- A Gale-Shapley state: a current matching plus the proposals already made.
structure GSState (P : Problem) where
  matching : Matching P
  -- proposals made in reverse order
  men_proposals : P.Men -> Finset P.Women

-- invariants
def man_prefers_final_match_to_all_non_proposees (σ : GSState P) (m : P.Men) : Prop :=
  let partner := σ.matching.menMatches m
  let p := σ.men_proposals m
  match partner with
  | none => True
  | some w => ∀ w' : P.Women, w' ∉ p →
    prefersOpt P.menPrefs m (some w) (some w')

def woman_prefers_final_match_to_all_suitors (σ : GSState P) (w : P.Women) : Prop :=
  let partner := σ.matching.womenMatches w
  ∀ m : P.Men, w ∈ σ.men_proposals m →
    partner = some m ∨ prefersOpt P.womenPrefs w partner (some m)

def state_satisfies_invariants (σ : GSState P) : Prop :=
  (∀ m : P.Men, man_prefers_final_match_to_all_non_proposees σ m) ∧
  (∀ w : P.Women, woman_prefers_final_match_to_all_suitors σ w)

-- Initial state: everyone unmatched and no proposals made.
def GSState.initial (P : Problem) : GSState P :=
  { matching :=
      { menMatches := fun _ => none
        womenMatches := fun _ => none },
    men_proposals := fun _ => {}}

-- Women a man can still propose to (acceptable and not yet proposed).
def candidateWomen (P : Problem) (σ : GSState P) (m : P.Men) : Finset P.Women := by
  classical
  letI := P.womenFintype
  exact Finset.univ.filter (fun w => P.menPrefs.acceptable m w ∧ ¬ (w ∈ σ.men_proposals m))

-- A free man who still has someone to propose to.
def isFree (P : Problem) (σ : GSState P) (m : P.Men) : Prop :=
  σ.matching.menMatches m = none ∧ (candidateWomen P σ m).Nonempty

-- A state is terminated if no man is free with someone left to propose to.
def terminated (P : Problem) (σ : GSState P) : Prop :=
  ¬ ∃ m, isFree P σ m

-- Choose an element from a nonempty finset.
def chooseFromFinset {α : Type*} (s : Finset α) (h : s.Nonempty) : α :=
  Classical.choose h

lemma chooseFromFinset_mem {α : Type*} (s : Finset α) (h : s.Nonempty) :
    chooseFromFinset s h ∈ s :=
  Classical.choose_spec h

-- Men compare women by "at least as preferred as": equality or strict preference.
def menPrefLE (P : Problem) (m : P.Men) (w1 w2 : P.Women) : Prop :=
  w1 = w2 ∨ P.menPrefs.prefers m w2 w1

-- The men-preference preorder is transitive.
lemma menPrefLE_trans (P : Problem) (m : P.Men) :
    IsTrans P.Women (menPrefLE P m) := by
  refine ⟨?_⟩
  intro a b c hab hbc
  cases hab with
  | inl hab =>
      subst hab
      exact hbc
  | inr hab =>
      cases hbc with
      | inl hbc =>
          subst hbc
          exact Or.inr hab
      | inr hbc =>
          exact Or.inr (P.menPrefs.prefers_trans m _ _ _ hbc hab)

-- Choose a maximal (most preferred) woman from the remaining candidates.
def chooseMaxCandidate (P : Problem) (σ : GSState P) (m : P.Men)
    (h : (candidateWomen P σ m).Nonempty) : P.Women := by
  classical
  letI : LE P.Women := ⟨menPrefLE P m⟩
  haveI : IsTrans P.Women (· ≤ ·) := menPrefLE_trans P m
  exact Classical.choose ((candidateWomen P σ m).exists_maximal h)

lemma chooseMaxCandidate_mem (P : Problem) (σ : GSState P) (m : P.Men)
    (h : (candidateWomen P σ m).Nonempty) :
    chooseMaxCandidate P σ m h ∈ candidateWomen P σ m := by
  classical
  letI : LE P.Women := ⟨menPrefLE P m⟩
  haveI : IsTrans P.Women (· ≤ ·) := menPrefLE_trans P m
  simpa using (Classical.choose_spec ((candidateWomen P σ m).exists_maximal h)).1

lemma chooseMaxCandidate_no_better (P : Problem) (σ : GSState P) (m : P.Men)
    (h : (candidateWomen P σ m).Nonempty) :
    ∀ w' ∈ candidateWomen P σ m,
      ¬ P.menPrefs.prefers m w' (chooseMaxCandidate P σ m h) := by
  classical
  letI : LE P.Women := ⟨menPrefLE P m⟩
  haveI : IsTrans P.Women (· ≤ ·) := menPrefLE_trans P m
  have hmax :
      Maximal (· ∈ candidateWomen P σ m) (chooseMaxCandidate P σ m h) := by
    simpa using (Classical.choose_spec ((candidateWomen P σ m).exists_maximal h))
  intro w' hw' hpref
  have hle : menPrefLE P m (chooseMaxCandidate P σ m h) w' := Or.inr hpref
  have hle' := hmax.2 hw' hle
  cases hle' with
  | inl hEq =>
      subst hEq
      exact (P.menPrefs.prefers_irrefl m _) hpref
  | inr hpref' =>
      have := P.menPrefs.prefers_trans m _ _ _ hpref' hpref
      exact (P.menPrefs.prefers_irrefl m _) this

lemma chooseMaxCandidate_is_acceptable (σ : GSState P) (m : P.Men)
  (h : (candidateWomen P σ m).Nonempty) :
  P.menPrefs.acceptable m (chooseMaxCandidate P σ m h) := by
  set w := chooseMaxCandidate P σ m h with w_eq
  have w_candidate : w ∈ candidateWomen P σ m := by
    exact chooseMaxCandidate_mem P σ m h
  unfold candidateWomen at w_candidate
  grind

def woman_is_better_than_all_candidates (σ : GSState P) (m : P.Men) (w : P.Women) : Prop :=
  ∀ w' ∈ candidateWomen P σ m, w' ≠ w → prefersOpt P.menPrefs m (some w) (some w')

-- Match m with w when w is currently unmatched.
def Matching.matchUnmatched
    (P : Problem) (μ : Matching P) (m : P.Men) (w : P.Women) : Matching P := by
  classical
  exact
    { menMatches := Function.update μ.menMatches m (some w)
      womenMatches := Function.update μ.womenMatches w (some m) }

-- Swap m in for mOld when w prefers m to mOld.
def Matching.swapMatch
    (P : Problem) (μ : Matching P) (m mOld : P.Men) (w : P.Women) :
    Matching P := by
  classical
  exact
    { menMatches := Function.update (Function.update μ.menMatches m (some w)) mOld none
      womenMatches := Function.update μ.womenMatches w (some m) }

-- One proposal step with an explicit proposer and recipient.
def GSState.stepWith (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women) : GSState P :=
  let men_proposals : P.Men -> Finset P.Women :=
    fun m' =>
      if m = m' then
        {w} ∪ (σ.men_proposals m)
      else
        σ.men_proposals m'
  match σ.matching.womenMatches w with
  | none =>
      if prefersOpt P.womenPrefs w (some m) none then
        { matching := Matching.matchUnmatched P σ.matching m w
          men_proposals := men_proposals}
      else
        { matching := σ.matching
          men_proposals := men_proposals}
  | some mOld =>
      if prefersOpt P.womenPrefs w (some m) (some mOld) then
        { matching := Matching.swapMatch P σ.matching m mOld w
          men_proposals := men_proposals}
      else
        { matching := σ.matching
          men_proposals := men_proposals}

-- One proposal step of the Gale-Shapley algorithm.
def GSState.step (P : Problem) (σ : GSState P) : GSState P :=
  if hfree : ∃ m, isFree P σ m then
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    GSState.stepWith P σ m w
  else
    σ

-- Iterate a fixed number of steps (bounded by number of proposals).
def GSState.runSteps (P : Problem) : Nat → GSState P
  | 0 => GSState.initial P
  | n + 1 => GSState.step P (GSState.runSteps P n)

-- Total number of possible proposals.
def proposalBound (P : Problem) : Nat := by
  classical
  letI := P.menFintype
  letI := P.womenFintype
  exact Fintype.card P.Men * Fintype.card P.Women

-- The Gale-Shapley matching after all proposals.
def galeShapley (P : Problem) : Matching P :=
  by
    classical
    exact (GSState.runSteps P (proposalBound P)).matching

end

end StableMarriageLean
