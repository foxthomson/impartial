import set_theory.ordinal
import impartial
import data.set

universes u v

open pgame

local infix ` ≈ ` := pgame.equiv

/-- The defineition of nim, nim O is the game where each player can move to nim O' where O' < O 
    If O is finite then this game can be veiwed as a pile of stones where each player can take a
	positie number of stones from it on their turn -/
noncomputable def nim : ordinal → pgame
| O₁ := ⟨ O₁.out.α, O₁.out.α,
					λ O₂, have hwf : (ordinal.typein O₁.out.r O₂) < O₁, from begin nth_rewrite_rhs 0 ←ordinal.type_out O₁, exact ordinal.typein_lt_type _ _ end, nim (ordinal.typein O₁.out.r O₂),
					λ O₂, have hwf : (ordinal.typein O₁.out.r O₂) < O₁, from begin nth_rewrite_rhs 0 ←ordinal.type_out O₁, exact ordinal.typein_lt_type _ _ end, nim (ordinal.typein O₁.out.r O₂)⟩ 
using_well_founded {dec_tac := tactic.assumption}

@[simp] lemma nim_def (O : ordinal) : nim O = pgame.mk
					O.out.α O.out.α
					(λ O₂, nim (ordinal.typein O.out.r O₂))
					(λ O₂, nim (ordinal.typein O.out.r O₂)) :=
by rw nim

lemma nim_wf_lemma {O₁ : ordinal} (O₂ : O₁.out.α) : (ordinal.typein O₁.out.r O₂) < O₁ :=
begin
	nth_rewrite_rhs 0 ← ordinal.type_out O₁, exact ordinal.typein_lt_type _ _
end

@[instance] lemma nim_impartial : ∀ (O : ordinal), impartial (nim O)
| O := 
begin
	rw pgame.impartial_def,
	rw nim_def,
	rw pgame.neg_def,
	split,
	split,
	{ rw pgame.le_def,
	  split,
		{ intro i,
			left,
		  use i,
			let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
			exact (@pgame.impartial_neg_equiv_self (nim (ordinal.typein O.out.r i)) (nim_impartial (ordinal.typein O.out.r i))).1 },
		{ intro j,
			right,
			use j,
			let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
			exact (@pgame.impartial_neg_equiv_self (nim (ordinal.typein O.out.r j)) (nim_impartial (ordinal.typein O.out.r j))).1 } },
	{ rw pgame.le_def,
		split,
		{ intro i,
			left,
			use i,
			let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
			exact (@pgame.impartial_neg_equiv_self (nim (ordinal.typein O.out.r i)) (nim_impartial (ordinal.typein O.out.r i))).2 },
		{ intro j,
			right,
			use j,
			let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
			exact (@pgame.impartial_neg_equiv_self (nim (ordinal.typein O.out.r j)) (nim_impartial (ordinal.typein O.out.r j))).2 } },
	split,
	{ intro i,
		rw pgame.move_left_mk,
		let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
		exact nim_impartial (ordinal.typein O.out.r i) },
	{ intro j,
		rw pgame.move_right_mk,
		let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
		exact nim_impartial (ordinal.typein O.out.r j) }
end
using_well_founded {dec_tac := tactic.assumption}

lemma nim_zero_p_position : (nim (0:ordinal.{u})).p_position :=
begin
	unfold1 nim,
	split;
	rw le_def_lt;
	split;
	intro i;
	try {rw left_moves_mk at i};
	try {rw right_moves_mk at i};
	try {	have h := ordinal.typein_lt_type (quotient.out (0:ordinal.{u})).r i,
				rw ordinal.type_out at h,
				have hcontra := ordinal.zero_le (ordinal.typein (quotient.out (0:ordinal)).r i),
				have h := not_le_of_lt h,
				contradiction };
	try { exact pempty.elim i }
end

lemma nim_non_zero_n_position (O : ordinal) (hO : O ≠ 0) : (nim O).n_position :=
begin
	unfold1 nim,
	rw ←ordinal.pos_iff_ne_zero at hO,
	let ps := ordinal.principal_seg_out hO,
	let O' := ps.top,
	split;
	rw lt_def_le,
	{ left,
		use O',
		rw move_left_mk,
		rw ordinal.typein_top,
		rw ordinal.type_out,
		exact nim_zero_p_position.2 },
	{ right,
		use O',
		rw move_right_mk,
		rw ordinal.typein_top,
		rw ordinal.type_out,
		exact nim_zero_p_position.1 }
end

lemma nim_sum_p_position_iff_eq (O₁ O₂ : ordinal) : (nim O₁ + nim O₂).p_position ↔ O₁ = O₂ :=
begin
	split,
	{ contrapose,
		intro hneq,
		intro hp,
		wlog h : O₁ ≤ O₂ using [O₁ O₂, O₂ O₁],
		exact ordinal.le_total O₁ O₂,
		{ have h : O₁ < O₂ := lt_of_le_of_ne h hneq,
			rw ←no_good_left_moves_iff_p_position at hp,
			let ps := ordinal.principal_seg_out h,
			-- let i := ps.top,
			equiv_rw left_moves_add (nim O₁) (nim O₂) at hp,
			rw nim_def O₂ at hp,
			specialize hp (sum.inr ps.top),
			unfold id at hp,
			rw add_move_left_inr at hp,
			rw move_left_mk at hp,
			rw ordinal.typein_top at hp,
			rw ordinal.type_out at hp,
			have hcontra := (impartial_add_self (nim O₁)).1,
			rw ←pgame.not_lt at hcontra,
			cases hp,
			contradiction }, 
		apply this,
			intro h,
			exact hneq h.symm,
		apply p_position_of_equiv,
		exact add_comm_equiv,
		assumption },
	{ intro h,
		rw h,
		exact impartial_add_self (nim O₂) }
end

lemma nim_sum_n_position_iff_neq (O₁ O₂ : ordinal) : (nim O₁ + nim O₂).n_position ↔ O₁ ≠ O₂ :=
begin
	split,
	{ intros hn heq,
		rw ←nim_sum_p_position_iff_eq at heq,
		cases hn,
		cases heq with h,
		rw ←pgame.not_lt at h,
		contradiction },
	{ contrapose,
		intro hnp,
		rw not_not,
		rw ←nim_sum_p_position_iff_eq,
		cases impartial_position_cases (nim O₁ + nim O₂),
		assumption,
		contradiction }
end

/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
	from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
	the image of the function. It is guarantied that the smallest ordinal not in the image will be
	in the set, i.e. we can use this to find the mex -/
def nonmoves {α : Type u} (M : α → ordinal.{u}) : set ordinal.{u} := { O : ordinal | ¬ ∃ a : α, M a = O }

lemma nonmoves_nonempty {α : Type u} (M : α → ordinal.{u}) : ∃ O : ordinal, O ∈ nonmoves M :=
begin
	classical,
	by_contra h,
	unfold nonmoves at h,
	simp at h,
	have hle : cardinal.univ.{u (u+1)} ≤ cardinal.lift.{u (u+1)} (cardinal.mk α),
		split,
		fconstructor,
		intro O,
		cases O,
		specialize h O,
		have hx := classical.indefinite_description _ h,
		split,
		exact hx.val,
		intros O₁ O₂,
		cases O₁,
		cases O₂,
		intro heq,
		injections_and_clear,
		simp at *, 
		ext,
		transitivity,
		symmetry,
		exact (classical.indefinite_description _ (h O₁)).prop,
		rw h_1,
		exact (classical.indefinite_description _ (h O₂)).prop,

	have hlt : cardinal.lift.{u (u+1)} (cardinal.mk α) < cardinal.univ.{u (u+1)},
		rw cardinal.lt_univ,
		use cardinal.mk α,
	
	cases hlt,
	contradiction
end

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the game is equivalent to -/
noncomputable def Grundy_value : Π (G : pgame.{u}) [G.impartial], ordinal.{u}
| G :=
begin
	introI,
	let M := λ i, Grundy_value (G.move_left i),
	exact ordinal.omin (nonmoves M) (nonmoves_nonempty M),
end
using_well_founded {dec_tac := pgame_wf_tac}

lemma Grundy_value_def (G : pgame) [G.impartial] : Grundy_value G = ordinal.omin (nonmoves (λ i, Grundy_value (G.move_left i))) (nonmoves_nonempty (λ i, Grundy_value (G.move_left i))) :=
begin
	rw Grundy_value,
	refl
end

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of nim, namely the game of nim corresponding to the games Grundy value -/
theorem Sprague_Grundy : ∀ (G : pgame.{u}) [_h : G.impartial], G ≈ nim (@Grundy_value G _h)
| G := 
begin
	classical,
	introI,
	rw equiv_iff_sum_p_position,
	rw ←no_good_left_moves_iff_p_position,
	intro i,
	equiv_rw left_moves_add G (nim $ Grundy_value G) at i,
	cases i with i₁ i₂,
	{ rw add_move_left_inl,
		apply n_position_of_equiv,
		apply add_congr,
		exact (Sprague_Grundy $ G.move_left i₁).symm,
		refl,
		rw nim_sum_n_position_iff_neq,
		intro heq,
		have heq := symm heq,
		rw Grundy_value_def G at heq,
		have h := ordinal.omin_mem (nonmoves (λ (i : G.left_moves), Grundy_value (G.move_left i))) (nonmoves_nonempty _),
		rw heq at h,
		have hcontra : ∃ (i' : G.left_moves), (λ (i'' : G.left_moves), Grundy_value (G.move_left i'')) i' = Grundy_value (G.move_left i₁) := ⟨ i₁, rfl ⟩,
		contradiction },
	{ rw add_move_left_inr,
		rw ←good_left_move_iff_n_position,
		revert i₂,
		rw nim_def,
		intro i₂,

		have h' : ∃ i : G.left_moves, (Grundy_value $ G.move_left i) = ordinal.typein (quotient.out $ Grundy_value G).r i₂,
		{ have hlt : ordinal.typein (quotient.out $ Grundy_value G).r i₂ < ordinal.type (quotient.out $ Grundy_value G).r := ordinal.typein_lt_type _ _,
			rw ordinal.type_out at hlt,
			revert i₂ hlt,
			rw Grundy_value_def,
			intros i₂ hlt,
			have hnotin : ordinal.typein (quotient.out (ordinal.omin (nonmoves (λ (i : G.left_moves), Grundy_value (G.move_left i))) _)).r i₂ ∉ (nonmoves (λ (i : G.left_moves), Grundy_value (G.move_left i))),
			{ intro hin,
				have hge := ordinal.omin_le hin,
				have hcontra := (le_not_le_of_lt hlt).2,
				contradiction },
			unfold nonmoves at hnotin,
			simpa using hnotin },
		
		cases h' with i hi,
		use (left_moves_add _ _).symm (sum.inl i),
		rw add_move_left_inl,
		rw move_left_mk,
		apply p_position_of_equiv,
		apply add_congr,
		symmetry,
		exact Sprague_Grundy (G.move_left i),
		refl,
		rw hi,
		exact impartial_add_self _ }
end
using_well_founded {dec_tac := pgame_wf_tac}