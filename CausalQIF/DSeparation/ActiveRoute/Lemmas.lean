import CausalQIF.DSeparation.ActiveRoute.Basic

open Finset

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

namespace ActiveRoute

/-- The list of a `cons` path starts with the source node. -/
lemma toList_toTrailT_cons {G : Graph.DAG V} {Z : Finset V} {s t u : V × TrailDir}
    (step : BayesBallStepT G Z s t) (rest : BayesBallPathT G Z t u) :
    (toTrailT (BayesBallPathT.cons step rest)).toList = s.1 :: (toTrailT rest).toList := by
  cases step with
  | step hEdge hopen =>
      rename_i v w arrival departure
      cases departure <;> simp [toTrailT, trailOfStep, Trail.append, Trail.toList]

/-- The list of a constructed trail starts with the path source. -/
lemma toList_toTrailT_starts {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (p : BayesBallPathT G Z s t) :
    ∃ xs, (toTrailT p).toList = s.1 :: xs := by
  cases p with
  | nil _ =>
      exact ⟨[], by simp [toTrailT, Trail.toList]⟩
  | cons step rest =>
      exact ⟨(toTrailT rest).toList, toList_toTrailT_cons step rest⟩

omit [DecidableEq V] [Fintype V] in
lemma hasTriple_cons_iff {xs : List V} {x a b c : V} :
    hasTriple (x :: xs) a b c ↔
      (x = a ∧ ∃ post : List V, xs = b :: c :: post) ∨ hasTriple xs a b c := by
  constructor
  · intro h
    rcases h with ⟨pre, post, hlist⟩
    cases pre with
    | nil =>
        simp at hlist
        rcases hlist with ⟨hxa, hxs⟩
        exact Or.inl ⟨hxa, ⟨post, hxs⟩⟩
    | cons p ps =>
        right
        refine ⟨ps, post, ?_⟩
        simp [List.cons_append] at hlist
        exact hlist.2
  · intro h
    rcases h with hhead | htail
    · rcases hhead with ⟨hxa, post, hxs⟩
      refine ⟨[], post, ?_⟩
      simp [hxa, hxs]
    · exact hasTriple.cons htail

/-- Helper: a list of length at most two contains no triple. -/
lemma not_trailBlocked_of_short_list {G : Graph.DAG V} {Z : Finset V} {xs : List V}
    (hlen : xs.length ≤ 2) :
    ¬ trailBlocked G Z xs := by
  intro h
  rcases h with ⟨a, b, c, htriple, _⟩
  rcases htriple with ⟨pre, post, hlist⟩
  have hlen2 : xs.length ≥ 3 := by
    calc xs.length = (pre ++ a :: b :: c :: post).length := by rw [hlist]
         _ = pre.length + 3 + post.length := by
              simp [List.length_append, List.length_cons]
              omega
         _ ≥ 3 := by omega
  omega

/-- The constructed `Type`-valued trail is never blocked by `Z`. -/
theorem toTrailT_not_blocked {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (p : BayesBallPathT G Z s t) :
    ¬ (toTrailT p).isBlocked Z := by
  induction p with
  | nil s =>
      simpa [Trail.isBlocked, toTrailT, Trail.toList] using
        (not_trailBlocked_of_short_list (G := G) (Z := Z) (xs := [s.1]) (by simp))
  | cons step rest ih =>
      rename_i start mid finish
      intro hblocked
      unfold Trail.isBlocked at hblocked
      rcases hblocked with ⟨a, b, c, htriple, hblocked_abc⟩
      have htriple' : hasTriple (start.1 :: (toTrailT rest).toList) a b c := by
        simpa [toList_toTrailT_cons step rest] using htriple
      rcases (hasTriple_cons_iff.mp htriple') with hhead | htail
      · rcases hhead with ⟨ha, post, htailList⟩
        cases rest with
        | nil mid =>
            have hlen := congrArg List.length htailList
            simp [toTrailT, Trail.toList] at hlen
        | cons step₂ rest₂ =>
            cases step with
            | step hEdge hopen =>
                cases step₂ with
                | step hEdge₂ hopen₂ =>
                    have hrestList :=
                      toList_toTrailT_cons (BayesBallStepT.step hEdge₂ hopen₂) rest₂
                    rw [hrestList] at htailList
                    injection htailList with hb htailRest
                    rcases toList_toTrailT_starts rest₂ with ⟨xs, hstarts⟩
                    rw [hstarts] at htailRest
                    injection htailRest with hc _
                    subst a
                    subst b
                    subst c
                    exact hopen₂
                      ((directionalTripleBlocked_iff_tripleBlocked hEdge hEdge₂).mpr hblocked_abc)
      · exact ih (by
          unfold Trail.isBlocked
          exact ⟨a, b, c, htail, hblocked_abc⟩)

/-- Every ActiveRoute yields an active, non-blocked Trail witness. -/
theorem to_activeTrail {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (route : ActiveRoute G Z s t) :
    ∃ tr : Trail G s.1 t.1, ¬ tr.isBlocked Z :=
  ⟨toTrail route.path, toTrailT_not_blocked (bayesBallPathT_of_bayesBallPath route.path)⟩

end ActiveRoute

end

end CausalQIF.DSeparation
