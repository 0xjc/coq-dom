Require Import Bool Arith List Omega.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require FMapList.
Require FMapFacts.
Require Import Classical.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.
Require Import Sorting.Permutation.
Import ListNotations.
Require Import BinInt.
Require Import Coq.Logic.FunctionalExtensionality.
Delimit Scope Int_scope with I.
Local Open Scope Z_scope.
(* Include Z. *)


(* == Graphics model. == *)

Inductive color :=
| Rgb : Z -> Z -> Z -> color
| None_c.

Definition red   := Rgb 255 0 0.
Definition green := Rgb 0 255 0.
Definition blue  := Rgb 0 0 255.

Inductive coordinate := Coordinate : forall x y : Z, coordinate.
Inductive dimension := Dimension : forall w h : Z, dimension.
Notation Coord := Coordinate.
Notation Dim := Dimension.
Definition c0 := Coord 0 0.
Definition add_c c1 c2 := match c1, c2 with
| Coord x y, Coord x' y' => Coord (x + x') (y + y')
end.

Definition graphic := coordinate -> color.

Definition blank : graphic := fun _ => None_c.

Definition composite base overlay offset : graphic := fun coord =>
  match offset, coord with
  | Coord x y, Coord x' y' =>
    let overlay_color := overlay (Coord (-x + x') (-y + y')) in
    match overlay_color with
    | None_c => base coord
    | _ => overlay_color
    end
  end.

Definition composite0 base overlay := composite base overlay c0.

Notation "base 'CC' overlay @ offset" := (composite base overlay offset) (at level 20, left associativity).
Notation "base 'C0' overlay" := (composite0 base overlay) (at level 20, left associativity).

Lemma composite_assoc : forall g1 g2 o1 g3 o2,
  g1 CC (g2 CC g3 @ o2) @ o1 = (g1 CC g2 @ o1) CC g3 @ (add_c o1 o2).
(*   composite g1 (composite g2 g3 o2) o1 = composite (composite g1 g2 o1) g3 (add_c o1 o2). *)
Proof.
  intros.
  extensionality x.
  destruct o1, o2, x.
  simpl.
  assert (- x1 + (- x0 + x) = - (x0 + x1) + x) by ring.
  assert (- y0 + (- y + y1) = - (y + y0) + y1) by ring.
  rewrite H.
  rewrite H0.
  destruct (g3 (Coord (- (x0 + x1) + x) (- (y + y0) + y1))); auto.
Qed.

Definition in_box x0 y0 w h x y : Prop :=
  x0 <= x /\ x < x0 + w /\ y0 <= y /\ y < y0 + h.

(* Let intuition make a big decision procedure that compares things. *)
Definition in_box_dec x0 y0 w h x y :
  let ib := in_box x0 y0 w h x y in {ib} + {~ib}.
Proof.
  simpl; unfold in_box.
  destruct (Z_le_dec x0 x); destruct (Z_lt_dec x (x0 + w));
    destruct (Z_le_dec y0 y); destruct (Z_lt_dec y (y0 + h));
      intuition auto.
Defined.
(* Print in_box_dec. *)

Definition clip g off dim : graphic := fun coord =>
  match off, dim, coord with
  | Coord x0 y0, Dim w h, Coord x y =>
    if (in_box_dec x0 y0 w h x y) then g coord else None_c
  end.

Definition blank_in g x0 y0 w h := forall x y,
    in_box x0 y0 w h x y -> g (Coord x y) = None_c.

(* Clipping to a region that's blank gives the blank graphic. *)
Lemma blank_clip : forall g x0 y0 w h,
    blank_in g x0 y0 w h -> clip g (Coord x0 y0) (Dim w h) = blank.
Proof.
  intros.
  unfold blank_in in *.
  extensionality x.
  destruct x.
  simpl.
  destruct in_box_dec; intuition.
Qed.

Definition solid c : graphic := fun _ => c.

(* Makes a solid box graphic at the origin. *)
Definition box dim c : graphic := clip (solid c) c0 dim.

(* Printing makes triples of width, height, and a list of (x, y, color) triples. *)
Definition pixel : Set := Z * Z * color.

Definition range_exc n := map (Z.of_nat) (seq 0 (Z.to_nat n)).

Definition print (g : graphic) w h :=
  let coordinates := list_prod (range_exc w) (range_exc h) in
  let expand_coordinate := fun xy => match xy with
  | (x, y) => (x, y, g (Coord x y))
  end in
  (w, h, map expand_coordinate coordinates).


Lemma clip_zero : forall (coord coord' : coordinate) (g : graphic),
  (clip g coord (Dim 0 0)) coord' = None_c.
Proof.
  intros.
  destruct coord.
  destruct coord'.
  simpl.
  destruct in_box_dec; unfold in_box in *.
  - omega.
  - auto.
Qed.


(* == DOM model. == *)

Inductive position := Static | Relative | Absolute.
Inductive overflow := Visible | Hidden.
Inductive attributes :=
  Attributes : forall
    (left top width height : Z)
    (color : color)
    (pos : position)
    (ovf : overflow),
    attributes.

Inductive dom : Set :=
| Dom : attributes -> forall (child sibling : dom), dom
| None_d.

(*
Definition dl dom := match dom with Dom (Attributes l _ _ _ _ _) _ _ => l end.
Definition dt dom := match dom with Dom (Attributes _ t _ _ _ _) _ _ => t end.
Definition dw dom := match dom with Dom (Attributes _ _ w _ _ _) _ _ => w end.
Definition dh dom := match dom with Dom (Attributes _ _ _ h _ _) _ _ => h end.
Definition dc dom := match dom with Dom (Attributes _ _ _ _ c _) _ _ => c end.
Definition dp dom := match dom with Dom (Attributes _ _ _ _ _ p) _ _ => p end.*)
(*Definition dchild dom := match dom with Dom _ child _ => child end.
Definition dsib dom := match dom with Dom _ _ sib => sib end.
*)

Function dom_size d := match d with
| Dom _ child sib => 1 + dom_size child + dom_size sib
| None_d => 0
end.


(* == Reference DOM renderer. == *)

(* Args:
   - Dom
   - Base graphic
   - Position for static layout
   - Base for absolute positions
   - Whether this pass is for static elements. *)
(* Return:
   - Rendered graphic
   - Position for next static sibling. *)
Function render_with_overflow dom g pos base (is_static : bool) : graphic :=
  match dom, pos, base with
  | None_d, _, _ => g
  | Dom (Attributes l t w h c p o) child sib, Coord x y, Coord x0 y0 =>
    let bg := box (Dim w h) c in
    match p with
    | Static =>
      let g := if is_static then composite g bg pos else g in
      let g := if is_static then render_with_overflow child g pos base true else g in
      render_with_overflow sib g (Coord x (y + h)) base is_static
    | Relative =>
      let pos' := Coord (x + l) (y + t) in
      let g := if is_static then g else composite g bg pos' in
      (* Do a static pass, then a positioned pass. *)
      let g := if is_static then g else render_with_overflow child g pos' pos' true in
      let g := if is_static then g else render_with_overflow child g pos' pos' false in
      render_with_overflow sib g (Coord x (y + h)) base is_static
    | Absolute =>
      let pos' := Coord l t in
      let g := if is_static then g else composite g bg pos' in
      (* Do a static pass, then a positioned pass. *)
      let g := if is_static then g else render_with_overflow child g pos' pos' true in
      let g := if is_static then g else render_with_overflow child g pos' pos' false in
      render_with_overflow sib g pos base is_static
    end
  end.

Definition clip_ovf (ovf : overflow) off dim g : graphic :=
  match ovf with
  | Visible => g
  | Hidden => clip g off dim
  end.

(* Args:
   - Dom
   - Base graphic
   - Position for static layout relative to the absolute base
   - Base for absolute positions
   - Whether this pass is for static elements. *)
(* Return:
   - Rendered graphic
   - Position for next static sibling. *)

Function render_statics dom pos : graphic :=
  match dom, pos with
  | None_d, _ => blank
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    match p with
    | Static =>
      blank CC (box (Dim w h) c) @ pos
            C0 (clip_ovf o pos (Dim w h) (render_statics child pos))
            C0 (render_statics sib (Coord x (y + h)))
    | Relative =>
      render_statics sib (Coord x (y + h))
    | Absolute =>
      render_statics sib pos
    end
  end.

Function render' dom pos : graphic :=
  match dom, pos with
  | None_d, _ => blank
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    match p with
    | Static =>
      (clip_ovf o pos (Dim w h) (render' child pos))
        C0 (render' sib (Coord x (y + h)))
    | Relative => (* Do a static pass, then a positioned pass. *)
      let pos' := Coord (x + l) (y + t) in
      clip_ovf o pos' (Dim w h)
        (blank CC (box (Dim w h) c) @ pos'
               CC (render_statics child c0) @ pos'
               CC (render' child c0) @ pos')
        C0 (render' sib (Coord x (y + h)))
    | Absolute => (* Do a static pass, then a positioned pass. *)
      let pos' := Coord l t in
      clip_ovf o pos' (Dim w h)
        (blank CC (box (Dim w h) c) @ pos'
               CC (render_statics child c0) @ pos'
               CC (render' child c0) @ pos')
        C0 (render' sib pos)
    end
  end.

(* Only render DOMs with nice roots. *)
Definition is_good_dom d := match d with
| Dom (Attributes 0 0 _ _ (Rgb _ _ _) Absolute _) _ _ => true
| _ => false
end.

Definition render d := if is_good_dom d then render' d c0 else blank.

(* Equality of two doms up to static coords. *)
Inductive Eq_dom_utsc : dom -> dom -> Prop :=
| Eq_dom_utsc_eq : forall dom, Eq_dom_utsc dom dom
| Eq_dom_utsc_static :
    forall l1 l2 t1 t2 w h c o child sib,
    Eq_dom_utsc (Dom (Attributes l1 t1 w h c Static o) child sib)
                (Dom (Attributes l2 t2 w h c Static o) child sib).

Lemma static_coord_irrelevance dom1 dom2 pos:
  Eq_dom_utsc dom1 dom2 ->
  render' dom1 pos = render' dom2 pos.
Proof.
  intros; induction H; auto.
Qed.

Inductive Color_in_graphic : color -> graphic -> Prop :=
| Cig_at : forall g pos, Color_in_graphic (g pos) g.
Hint Constructors Color_in_graphic.

Inductive Color_in_dom : color -> dom -> Prop :=
| Cid_here : forall l t w h c p o child sib,
             Color_in_dom c (Dom (Attributes l t w h c p o) child sib)
| Cid_child : forall c a child sib, Color_in_dom c child -> Color_in_dom c (Dom a child sib)
| Cid_sib : forall c a child sib, Color_in_dom c sib -> Color_in_dom c (Dom a child sib).
Hint Constructors Color_in_dom.

(* Only the None color is in the blank graphic. *)
Lemma color_in_blank c:
  Color_in_graphic c blank ->
  c = None_c.
Proof.
  intros; remember blank as g.
  destruct H; subst; auto.
Qed.

(* Only the background color is in the solid graphic. *)
Lemma color_in_solid c c':
  Color_in_graphic c (solid c') ->
  c = c'.
Proof.
  intros. remember (solid c') as g.
  destruct H; subst; auto.
Qed.

(* If a color (not None_c) is in a clipped graphic,
   then it is in the original graphic. *)
Lemma color_in_clip c g off dim:
  c <> None_c ->
  Color_in_graphic c (clip g off dim) ->
  Color_in_graphic c g.
Proof.
  intros.
  remember (clip g off dim) as g'.
  destruct H0; subst.
  destruct off as [x y].
  destruct dim as [w h].
  unfold clip.
  destruct pos.
  destruct (in_box_dec x y w h x0 y0).
  - auto.
  - contradict H.
    unfold clip.
    destruct (in_box_dec x y w h x0 y0); [contradiction | auto].
Qed.

Lemma color_in_clip_ovf c ovf off dim g:
  c <> None_c ->
  Color_in_graphic c (clip_ovf ovf off dim g) ->
  Color_in_graphic c g.
Proof.
  unfold clip_ovf.
  destruct ovf; [auto | apply color_in_clip].
Qed.

(* Only the background color or the None color is in a box graphic. *)
Lemma color_in_box c dim c':
  c <> None_c ->
  Color_in_graphic c (box dim c') ->
  c = c'.
Proof.
  intros.
  unfold box in H0.
  apply color_in_clip in H0; auto.
  apply color_in_solid in H0; auto.
Qed.

(* If a color is in the composition of two graphics,
   then it is in one of the components. *)
Lemma color_in_composite c g1 g2 pos:
  Color_in_graphic c (g1 CC g2 @ pos) ->
  Color_in_graphic c g1 \/ Color_in_graphic c g2.
Proof.
  intros.
  remember (g1 CC g2 @ pos) as g.
  unfold composite in Heqg.
  destruct pos as [x y].
  destruct H.
  destruct pos as [x' y'].
  subst.
  remember (g2 (Coord (- x + x') (- y + y'))) as c.
  destruct c; [rewrite Heqc|]; auto.
Qed.

Ltac destruct_color_in H :=
  repeat
    ((apply color_in_composite in H; destruct H) ||
     (apply color_in_clip_ovf in H; auto) ||
     (apply color_in_blank in H; try contradiction) ||
     (apply color_in_box in H; subst; auto)).

Lemma color_in_render_statics color dom pos:
  color <> None_c ->
  Color_in_graphic color (render_statics dom pos) ->
  Color_in_dom color dom.
Proof.
  intro; revert pos.
  induction dom as [attrs child IHchild sib IHsib |].
  2: simpl; intros; apply color_in_blank in H0; contradiction.
  destruct attrs as [l t w h c' p o].
  destruct pos as [x y].
  destruct p; simpl in *; intros;
    destruct_color_in H0;
    try (pose (IHchild _ H0); auto);
    try (pose (IHsib _ H0); auto).
Qed.

Lemma color_in_render' color dom pos:
  color <> None_c ->
  Color_in_graphic color (render' dom pos) ->
  Color_in_dom color dom.
Proof.
  intro; revert pos.
  induction dom as [attrs child IHchild sib IHsib |].
  2: simpl; intros; apply color_in_blank in H0; contradiction.
  destruct attrs as [l t w h c' p o].
  destruct pos as [x y].
  destruct p; simpl in *; intros;
    destruct_color_in H0;
    try (pose (IHchild _ H0); auto);
    try (pose (IHsib _ H0); auto);
    try (pose (color_in_render_statics _ _ _ H H0); auto).
Qed.


                                                               
Definition green_middle := Dom (Attributes 5 0 55 40 green Relative Visible) None_d None_d.
Definition red_top_right := Dom (Attributes 5 5 20 20 red Static Visible) None_d green_middle.
Definition test := Dom (Attributes 0 0 100 70 blue Absolute Hidden) red_top_right None_d.

Compute print (render test) 100 70.

(* Stupid optimization: no hidden overflows -> can paint directly *)

Inductive good_overflow : dom -> Prop :=
| Go_none : good_overflow None_d
| Go_node : forall a b l t w h c p, good_overflow a -> good_overflow b ->
  good_overflow (Dom (Attributes l t w h c p Visible) a b).
Hint Constructors good_overflow.

Definition good_overflow_dec : forall d, {good_overflow d} + {~(good_overflow d)}.
Proof.
  induction d.
  (* TODO: spamming tactic. *)
  - intuition; destruct a; destruct ovf; intuition; right; intros; inversion H; subst; intuition.
  - auto.
Qed.

(* Dumb optimization: don't clip on overflow. *)
Function stupid_renderer' dom pos (is_static : bool) : graphic :=
  match dom, pos with
  | None_d, _ => blank
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    let bg := box (Dim w h) c in
    match p, is_static with
    | Static, true =>
      let g := composite blank bg pos in
      let g_child := stupid_renderer' child pos true in
      let g := composite0 g g_child in
      let g_sib := stupid_renderer' sib (Coord x (y + h)) true in
      composite0 g g_sib
    | Static, false =>
      let g_child := stupid_renderer' child pos false in
      let g_sib := stupid_renderer' sib (Coord x (y + h)) false in
      composite0 g_child g_sib
    | Relative, true =>
      stupid_renderer' sib (Coord x (y + h)) true
    | Relative, false =>
      let pos' := Coord (x + l) (y + t) in
      let g := composite blank bg pos' in
      (* Do a static pass, then a positioned pass. *)
      let g_child := stupid_renderer' child c0 true in
      let g := (composite g g_child pos') in
      let g_child := stupid_renderer' child c0 false in
      let g := (composite g g_child pos') in
      let g_sib := stupid_renderer' sib (Coord x (y + h)) false in
      composite0 g g_sib
    | Absolute, true =>
      stupid_renderer' sib pos true
    | Absolute, false =>
      let pos' := Coord l t in
      let g := composite blank bg pos' in
      (* Do a static pass, then a positioned pass. *)
      let g_child := stupid_renderer' child c0 true in
      let g := (composite g g_child pos') in
      let g_child := stupid_renderer' child c0 false in
      let g := (composite g g_child pos') in
      let g_sib := stupid_renderer' sib pos false in
      composite0 g g_sib
    end
  end.

Definition stupid_render d := if is_good_dom d then stupid_renderer' d c0 false else blank.

Lemma asdf : forall d, good_overflow d -> render' d = stupid_renderer' d.
Proof.
  intros.
  induction d; auto.
  inversion H.
  subst.
  intuition.
  simpl.
  rewrite <- H0.
  rewrite <- H1.
  auto.
Qed.


(* Instead of making a fresh graphic, paint on a graphic at an offset. *)
Function whatever_render' dom pos g offset (is_static : bool) : graphic :=
  match dom, pos, offset with
  | None_d, _, _ => blank
  | Dom (Attributes l t w h c p o) child sib, Coord x y, Coord x0 y0 =>
    let bg := box (Dim w h) c in
    match p, is_static with
    | Static, true =>
      let g := composite g bg (add_c pos offset) in
      let g := whatever_render' child pos g offset true in
      whatever_render' sib (Coord x (y + h)) g offset true
    | Static, false =>
      let g := whatever_render' child pos g offset false in
      whatever_render' sib (Coord x (y + h)) g offset false
    | Relative, true =>
      whatever_render' sib (Coord x (y + h)) g offset true
    | Relative, false =>
      let pos' := Coord (x + l) (y + t) in
      let g := composite g bg (add_c pos' offset) in
      (* Do a static pass, then a positioned pass. *)
      let g := whatever_render' child c0 g (add_c pos' offset) true in
      let g := whatever_render' child c0 g (add_c pos' offset) false in
      whatever_render' sib (Coord x (y + h)) g offset false
    | Absolute, true =>
      whatever_render' sib pos g offset true
    | Absolute, false =>
      let pos' := Coord l t in
      let g := composite g bg (add_c pos' offset) in
      (* Do a static pass, then a positioned pass. *)
      let g := whatever_render' child c0 g (add_c pos' offset) true in
      let g := whatever_render' child c0 g (add_c pos' offset) false in
      whatever_render' sib pos g offset false
    end
  end.

Definition whatever_render d :=
  if is_good_dom d then whatever_render' d c0 blank c0 false else blank.

Compute print (whatever_render test) 100 70.

Lemma whatever : forall d, good_overflow d -> render d = whatever_render d.
Proof.
  intros.
Admitted.