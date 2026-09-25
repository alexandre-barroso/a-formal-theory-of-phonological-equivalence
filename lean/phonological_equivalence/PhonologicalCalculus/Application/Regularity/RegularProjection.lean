                     
                   
import PhonologicalCalculus.Application.Regularity.ReferenceWindows
import PhonologicalCalculus.Application.Regularity.LocalScore

namespace RegularProjection

variable {A B Q : Type}

def imageNFA (M : DFA A Q) (f : A → B) : NFA B Q where
  start := {M.start}
  accept := M.accept
  step := fun q b => {r | ∃ a, f a = b ∧ M.step q a = r}

theorem image_eval (M : DFA A Q) (f : A → B) (bs : List B) (S : Set Q) (q : Q) :
    q ∈ (imageNFA M f).evalFrom S bs ↔
      ∃ p ∈ S, ∃ xs, xs.map f = bs ∧ M.evalFrom p xs = q := by
  induction bs generalizing S q with
  | nil => simp
  | cons b bs ih =>
    rw [NFA.evalFrom_cons,ih]
    constructor
    · rintro ⟨r,hr,xs,hxs,hq⟩
      rcases NFA.mem_stepSet.mp hr with ⟨p,hp,a,ha,he⟩
      refine ⟨p,hp,a :: xs,by simp [ha,hxs],?_⟩
      simpa [DFA.evalFrom_cons,he] using hq
    · rintro ⟨p,hp,xs,hxs,hq⟩
      rcases List.map_eq_cons_iff.mp hxs with ⟨a,ys,rfl,ha,hy⟩
      refine ⟨M.step p a,?_,ys,hy,hq⟩
      apply NFA.mem_stepSet.mpr
      exact ⟨p,hp,a,ha,rfl⟩

theorem image_accepts (M : DFA A Q) (f : A → B) :
    (imageNFA M f).accepts = List.map f '' M.accepts := by
  ext bs
  rw [NFA.mem_accepts]
  change (∃ q ∈ M.accept, q ∈ (imageNFA M f).evalFrom {M.start} bs) ↔ _
  simp only [image_eval,Set.mem_singleton_iff,exists_eq_left]
  constructor
  · rintro ⟨q,hq,xs,hxs,he⟩
    refine ⟨xs,?_,hxs⟩
    change M.evalFrom M.start xs ∈ M.accept
    rwa [he]
  · rintro ⟨xs,hx,hxs⟩
    exact ⟨M.eval xs,hx,xs,hxs,rfl⟩

theorem regular_image {L : Language A} (h : L.IsRegular) (f : A → B) :
    Language.IsRegular (List.map f '' L) := by
  classical
  rcases h with ⟨Q,hQ,M,rfl⟩
  exact ⟨Set Q,inferInstance,(imageNFA M f).toDFA,by rw [NFA.toDFA_correct,image_accepts]⟩

variable {S O : Type}

abbrev Token (S O : Type) := Sum (ReferenceWindows.Window S) (ReferenceWindows.Window S × O)

def input (t : Token S O) : ReferenceWindows.Window S := Sum.elim id Prod.fst t
def output (t : Token S O) : Option O := Sum.elim (fun _ => none) (some ∘ Prod.snd) t
def raw (t : Token S O) : S × Option O := ((input t).c,output t)

def nativeScore
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (xs : List (Token S O)) : ℕ :=
  LocalScore.deleteCost del xs + LocalScore.objective f none none ((LocalScore.survivors xs).map some)

def nativeWinner
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) (xs : List (Token S O)) : Prop :=
  ReferenceWindows.valid (xs.map input) ∧ (∀ t ∈ xs, ok (input t).c (output t)) ∧
    ∀ ys, ReferenceWindows.valid (ys.map input) → (∀ t ∈ ys, ok (input t).c (output t)) →
      ys.map (fun t => (input t).c) = xs.map (fun t => (input t).c) →
      nativeScore f del xs ≤ nativeScore f del ys

theorem native_winner_iff
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) (xs : List (Token S O)) :
    nativeWinner f del ok xs ↔ ReferenceWindows.valid (xs.map input) ∧
      (∀ t ∈ xs, ok (input t).c (output t)) ∧ ∀ ys, (∀ t ∈ ys, ok (input t).c (output t)) →
      ys.map input = xs.map input → nativeScore f del xs ≤ nativeScore f del ys := by
  constructor
  · rintro ⟨hv,ha,hw⟩
    refine ⟨hv,ha,fun ys hy he => hw ys ?_ hy ?_⟩
    · simpa [he] using hv
    · simpa [List.map_map,Function.comp_def] using congrArg (List.map ReferenceWindows.Window.c) he
  · rintro ⟨hv,ha,hw⟩
    refine ⟨hv,ha,fun ys hys hya he => hw ys hya ?_⟩
    apply ReferenceWindows.window_unique hys hv
    simpa [List.map_map,Function.comp_def] using he

theorem regular_native_alignments [Fintype S] [Fintype O]
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) :
    Language.IsRegular (List.map raw '' {xs | nativeWinner f del ok xs}) := by
  apply regular_image
  have hv := ReferenceWindows.regular_comap (ReferenceWindows.regular_valid (S := S)) (input (S := S) (O := O))
  have hw := LocalScore.integer_local_regularity f del input (fun t => ok (input t).c (output t))
  have hi := hv.inf hw
  convert hi using 1
  ext xs
  exact native_winner_iff f del ok xs

end RegularProjection
