Require Import Bool Arith List Omega.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Relation_Operators.
(* Require FMapList.
Require FMapFacts. *)
Require Import Classical.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.
(* Require Import Sorting.Permutation. *)
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

Definition black   := Rgb 0 0 0.
Definition red     := Rgb 255 0 0.
Definition green   := Rgb 0 255 0.
Definition blue    := Rgb 0 0 255.
Definition yellow  := Rgb 255 255 0.
Definition magenta := Rgb 255 0 255.
Definition cyan    := Rgb 0 255 255.
Definition white   := Rgb 255 255 255.
(* None_c will show as gray on the HTML renderer *)

Inductive coordinate := Coordinate : forall x y : Z, coordinate.
Inductive dimension := Dimension : forall w h : Z, dimension.
Notation Coord := Coordinate.
Notation Dim := Dimension.
Definition c0 := Coord 0 0.
Definition d0 := Dim 0 0.

Definition add_c c1 c2 := match c1, c2 with
| Coord x y, Coord x' y' => Coord (x + x') (y + y')
end.
Definition subtr_c c1 c2 := match c1, c2 with
| Coord x y, Coord x' y' => Coord (x - x') (y - y')
end.

Lemma add_c0 c : add_c c c0 = c.
Proof. destruct c; simpl; ring_simplify (x + 0) (y + 0); auto. Qed.
Lemma subtr_c0 c : subtr_c c c0 = c.
Proof. destruct c; simpl; ring_simplify (x - 0) (y - 0); auto. Qed.

Definition graphic := coordinate -> color.
Definition solid c : graphic := fun _ => c.
Definition blank := solid None_c.

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

Notation "base 'CC' overlay @ offset" :=
  (composite base overlay offset) (at level 20, left associativity).
Notation "base 'C0' overlay" :=
  (composite0 base overlay) (at level 20, left associativity).

Lemma composite_assoc : forall g1 g2 o1 g3 o2,
  g1 CC (g2 CC g3 @ o2) @ o1 = (g1 CC g2 @ o1) CC g3 @ (add_c o1 o2).
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

Lemma composite_blank : forall g off,
  g CC blank @ off = g.
Proof.
  intros; extensionality pos; destruct off, pos; auto.
Qed.

Lemma composite_onto_blank : forall g,
  blank CC g @ c0 = g.
Proof.
  intros; extensionality pos; destruct pos as [x y]; simpl.
  destruct (g (Coord x y)); auto.
Qed.

Definition in_box x0 y0 w h x y : Prop :=
  x0 <= x /\ x < x0 + w /\ y0 <= y /\ y < y0 + h.

(* Let intuition make a big decision procedure that compares things. *)
Definition in_box_dec x0 y0 w h x y :
  let ib := in_box x0 y0 w h x y in {ib} + {~ib}.
Proof.
  simpl; unfold in_box.
  destruct (Z_le_dec x0 x), (Z_lt_dec x (x0 + w)),
    (Z_le_dec y0 y), (Z_lt_dec y (y0 + h));
      intuition auto.
Defined.
(* Print in_box_dec. *)

Lemma in_box_shift x0 y0 w h x y a b:
  in_box x0 y0 w h x y <-> in_box (x0+a) (y0+b) w h (x+a) (y+b).
Proof.
  unfold in_box; intuition.
Qed.

Definition clip g off dim : graphic := fun coord =>
  match off, dim, coord with
  | Coord x0 y0, Dim w h, Coord x y =>
    if (in_box_dec x0 y0 w h x y) then g coord else None_c
  end.

Definition blank_in g x0 y0 w h := forall x y,
  in_box x0 y0 w h x y -> g (Coord x y) = None_c.

Lemma blank_clip : forall pos dim,
  clip blank pos dim = blank.
Proof.
  intros.
  extensionality x.
  destruct x.
  unfold blank, solid, clip.
  destruct pos, dim.
  destruct in_box_dec; auto.
Qed.

(* Clipping to a region that's blank gives the blank graphic. *)
Lemma blank_in_clip : forall g x0 y0 w h,
    blank_in g x0 y0 w h -> clip g (Coord x0 y0) (Dim w h) = blank.
Proof.
  intros.
  unfold blank_in in *.
  extensionality x.
  destruct x.
  simpl.
  destruct in_box_dec; intuition.
Qed.

(* Clipping to a region of zero dimension gives the blank graphic. *)
Lemma clip_zero : forall (coord coord' : coordinate) (g : graphic),
  clip g coord (Dim 0 0) = blank.
Proof.
  intros.
  destruct coord, coord'.
  extensionality pos; destruct pos; simpl.
  destruct in_box_dec; unfold in_box in *; auto; omega.
Qed.

Lemma clip_composite_distr g1 g2 offset pos dim:
  clip (g1 CC g2 @ offset) pos dim =
  (clip g1 pos dim) CC (clip g2 (subtr_c pos offset) dim) @ offset.
Proof.
  extensionality x.
  destruct x as [xt yt].
  destruct pos as [x y].
  destruct dim as [w h].
  destruct offset as [x' y'].
  simpl.
  repeat destruct in_box_dec; auto.
  - apply (in_box_shift _ _ _ _ _ _ (-x') (-y')) in i.
    ring_simplify (x + - x') in i.
    ring_simplify (y + - y') in i.
    replace (xt + - x') with (- x' + xt) in i by ring.
    replace (yt + - y') with (- y' + yt) in i by ring.
    contradiction.
  - apply (in_box_shift _ _ _ _ _ _ x' y') in i.
    ring_simplify in i.
    ring_simplify (x - x' + x') (y - y' + y') in i.
    contradiction.
Qed.

(* The building block of our simple DOM model.
   Makes a solid box graphic at an offset. *)
Definition box_at off dim c : graphic := clip (solid c) off dim.
Definition box := box_at c0.

(* Intersection of two boxes, forming another box (or the empty set).
   Used to compute nested clipping bounds. *)
Definition box_intersect off dim off' dim' :=
  match off, dim, off', dim' with
  | Coord x1 y1, Dim w1 h1, Coord x2 y2, Dim w2 h2 =>
    (Coord (Z.max x1 x2) (Z.max y1 y2),
     Dim (Z.min (x1+w1) (x2+w2) - Z.max x1 x2)
         (Z.min (y1+h1) (y2+h2) - Z.max y1 y2))
  end.

Local Ltac Z_maxmin H :=
  apply Z.max_l_iff in H || apply Z.max_r_iff in H ||
  apply Z.min_l_iff in H || apply Z.min_r_iff in H.

(* Proves that box_intersect is correct w.r.t. in_box.
   Stated directly to avoid annoying pair stuff. *)
Lemma box_intersect_equiv x1 y1 w1 h1 x2 y2 w2 h2 x y:
  in_box x1 y1 w1 h1 x y /\ in_box x2 y2 w2 h2 x y <->
  in_box (Z.max x1 x2) (Z.max y1 y2)
    (Z.min (x1+w1) (x2+w2) - Z.max x1 x2)
    (Z.min (y1+h1) (y2+h2) - Z.max y1 y2) x y.
Proof.
  unfold in_box.
  destruct (Z.max_dec x1 x2) as [Hx|Hx]; rewrite Hx;
  destruct (Z.max_dec y1 y2) as [Hy|Hy]; rewrite Hy;
  destruct (Z.min_dec (x1+w1) (x2+w2)) as [Hx'|Hx']; rewrite Hx';
  destruct (Z.min_dec (y1+h1) (y2+h2)) as [Hy'|Hy']; rewrite Hy';
  Z_maxmin Hx; Z_maxmin Hy; Z_maxmin Hx'; Z_maxmin Hy'; intuition omega.
Qed.

Local Ltac Z_commute_max n m :=
  replace (Z.max n m) with (Z.max m n) by apply Z.max_comm.
Local Ltac Z_commute_min n m :=
  replace (Z.min n m) with (Z.min m n) by apply Z.min_comm.

Lemma box_intersect_comm off dim off' dim':
  box_intersect off dim off' dim' =
  box_intersect off' dim' off dim.
Proof.
  (* can also be done by box_intersect_equiv *)
  unfold box_intersect.
  destruct off, dim, off', dim'.
  Z_commute_max x0 x.
  Z_commute_max y0 y.
  Z_commute_min (x0 + w0) (x + w).
  Z_commute_min (y0 + h0) (y + h).
  auto.
Qed.


(* Printing makes triples of width, height, and a list of (x, y, color) triples. *)
Definition pixel : Set := Z * Z * color.

Definition range_exc n := map (Z.of_nat) (seq 0 (Z.to_nat n)).

Definition print (g : graphic) w h :=
  let coordinates := list_prod (range_exc w) (range_exc h) in
  let expand_coordinate := fun xy => match xy with
  | (x, y) => (x, y, g (Coord x y))
  end in
  (w, h, map expand_coordinate coordinates).


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
(* Function render_with_overflow dom g pos base (is_static : bool) : graphic :=
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
  end. *)

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

Function render0 dom pos : graphic :=
  match dom, pos with
  | None_d, _ => blank
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    match p with
    | Static =>
      blank CC (box (Dim w h) c) @ pos
            C0 (clip_ovf o pos (Dim w h) (render0 child pos))
            C0 (render0 sib (Coord x (y + h)))
    | Relative =>
      render0 sib (Coord x (y + h))
    | Absolute =>
      render0 sib pos
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
               CC (render0 child c0) @ pos'
               CC (render' child c0) @ pos')
        C0 (render' sib (Coord x (y + h)))
    | Absolute => (* Do a static pass, then a positioned pass. *)
      let pos' := Coord l t in
      clip_ovf o pos' (Dim w h)
        (blank CC (box (Dim w h) c) @ pos'
               CC (render0 child c0) @ pos'
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

(* Testing the reference renderer.
   A red block followed by a green block on a black background.
   Both blocks have a yellow stripe inside, with different clipping behavior. *)
(* Definition yellow_stripe := Dom (Attributes 0 0 100 5 yellow Static Visible) None_d None_d.
Definition green_block := Dom (Attributes 5 0 55 40 green Relative Visible) yellow_stripe None_d.
Definition red_block := Dom (Attributes 5 5 20 20 red Static Hidden) yellow_stripe green_block.
Definition test := Dom (Attributes 0 0 100 70 black Absolute Hidden) red_block None_d. *)
Definition red_thing := Dom (Attributes 5 5 10 10 red Absolute Visible) None_d None_d.
Definition blue_thing := Dom (Attributes 5 5 10 10 blue Static Visible) None_d red_thing.
Definition green_middle := Dom (Attributes 5 0 55 40 green Relative Visible) blue_thing None_d.
Definition red_top_right := Dom (Attributes 5 5 20 20 red Static Visible) None_d green_middle.
Definition test := Dom (Attributes 0 0 100 70 blue Absolute Hidden) red_top_right None_d.

(* Compute print (render test) 100 70. *)


(* == Facts about the reference renderer == *)

(* Equality of two doms up to static coords. *)
Inductive Eq_dom_utsc : dom -> dom -> Prop :=
| Eq_dom_utsc_eq : forall dom, Eq_dom_utsc dom dom
| Eq_dom_utsc_static :
  forall l1 l2 t1 t2 w h c o child sib,
  Eq_dom_utsc (Dom (Attributes l1 t1 w h c Static o) child sib)
              (Dom (Attributes l2 t2 w h c Static o) child sib).

(* States that the l and t attributes of a Static dom element
   are irrelevant for the rendering. *)
Lemma static_coord_irrelevance dom1 dom2 pos:
  Eq_dom_utsc dom1 dom2 ->
  render' dom1 pos = render' dom2 pos.
Proof.
  intros; induction H; auto.
Qed.

(* Next, we show that if a color exists in the rendered graphic,
   then there must be a DOM element with that color. *)

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

Lemma color_in_render0 color dom pos:
  color <> None_c ->
  Color_in_graphic color (render0 dom pos) ->
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
    try (pose (color_in_render0 _ _ _ H H0); auto).
Qed.


(* == Stupid optimization ==
   no hidden overflows -> can paint directly *)

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
Function stupid_render0 dom pos : graphic :=
  match dom, pos with
  | None_d, _ => blank
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    match p with
    | Static =>
      blank CC (box (Dim w h) c) @ pos
            C0 (stupid_render0 child pos)
            C0 (stupid_render0 sib (Coord x (y + h)))
    | Relative =>
      stupid_render0 sib (Coord x (y + h))
    | Absolute =>
      stupid_render0 sib pos
    end
  end.

Function stupid_render' dom pos : graphic :=
  match dom, pos with
  | None_d, _ => blank
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    match p with
    | Static =>
      (stupid_render' child pos)
        C0 (stupid_render' sib (Coord x (y + h)))
    | Relative => (* Do a static pass, then a positioned pass. *)
      let pos' := Coord (x + l) (y + t) in
      (blank CC (box (Dim w h) c) @ pos'
             CC (stupid_render0 child c0) @ pos'
             CC (stupid_render' child c0) @ pos')
        C0 (stupid_render' sib (Coord x (y + h)))
    | Absolute => (* Do a static pass, then a positioned pass. *)
      let pos' := Coord l t in
      (blank CC (box (Dim w h) c) @ pos'
             CC (stupid_render0 child c0) @ pos'
             CC (stupid_render' child c0) @ pos')
        C0 (stupid_render' sib pos)
    end
  end.

Definition stupid_render d := if is_good_dom d then stupid_render' d c0 else blank.

Lemma stupid_render0_correct d pos:
  good_overflow d ->
  stupid_render0 d pos = render0 d pos.
Proof.
  intros; revert pos.
  induction d; auto.
  inversion_clear H.
  intuition.
  destruct pos as [x y].
  destruct p; simpl; auto.
  rewrite H, H2; auto.
Qed.

Lemma stupid_render'_correct d pos:
  good_overflow d ->
  stupid_render' d pos = render' d pos.
Proof.
  intros; revert pos.
  induction d; auto.
  inversion_clear H.
  intuition.
  destruct pos as [x y].
  destruct p; simpl; rewrite H, H2; try rewrite stupid_render0_correct; auto.
Qed.

(* == whatever_render ==
   Instead of making a fresh graphic, paint on a graphic at an offset.
   Note that clipping is applied directly to boxes, not to composited graphics.  *)

Inductive clip_directive : Set :=
| Don't_clip : clip_directive
| Clip_to : forall (pos : coordinate) (dim : dimension), clip_directive.

(* The next three functions are basically all just box_intersect. *)
Definition clip_intersect cd1 cd2 :=
  match cd1, cd2 with
  | Don't_clip, _ => cd2
  | _, Don't_clip => cd1
  | Clip_to pos1 dim1, Clip_to pos2 dim2 =>
    match (box_intersect pos1 dim1 pos2 dim2) with
    | (pos3, dim3) => Clip_to pos3 dim3
    end
  end.

Definition restrict_clip cd ovf pos dim :=
  match ovf with
  | Visible => cd
  | Hidden => clip_intersect cd (Clip_to pos dim)
  end.

Definition clip_box cd pos dim :=
  match cd with
  | Don't_clip => (pos, dim)
  | Clip_to pos1 dim1 => box_intersect pos1 dim1 pos dim
  end.

Function whatever_render0 dom pos cd g offset : graphic :=
  match dom, pos with
  | None_d, _ => g
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    match p with
    | Static =>
      let (bg_pos, bg_dim) := clip_box cd pos (Dim w h) in
      let g := g CC (box_at bg_pos bg_dim c) @ offset in
      let child_cd := restrict_clip cd o pos (Dim w h) in
      let g := whatever_render0 child pos child_cd g offset in
      whatever_render0 sib (Coord x (y + h)) cd g offset
    | Relative =>
      whatever_render0 sib (Coord x (y + h)) cd g offset
    | Absolute =>
      whatever_render0 sib pos cd g offset
    end
  end.

Function whatever_render' dom pos cd g offset : graphic :=
  match dom, pos with
  | None_d, _ => g
  | Dom (Attributes l t w h c p o) child sib, Coord x y =>
    match p with
    | Static =>
      let child_cd := restrict_clip cd o pos (Dim w h) in
      let g := whatever_render' child pos child_cd g offset in
      whatever_render' sib (Coord x (y + h)) cd g offset
    | Relative => (* Do a static pass, then a positioned pass. *)
      let pos' := Coord (x + l) (y + t) in
      let (bg_pos, bg_dim) := clip_box cd pos' (Dim w h) in
      let g := g CC (box_at bg_pos bg_dim c) @ offset in
      (* Do a static pass, then a positioned pass. *)
      let child_cd := restrict_clip cd o pos' (Dim w h) in
      let g := whatever_render0 child c0 child_cd g (add_c pos' offset) in
      let g := whatever_render' child c0 child_cd g (add_c pos' offset) in
      whatever_render' sib (Coord x (y + h)) cd g offset
    | Absolute => (* Do a static pass, then a positioned pass. *)
      let pos' := Coord l t in
      let (bg_pos, bg_dim) := clip_box cd pos' (Dim w h) in
      let g := g CC (box_at bg_pos bg_dim c) @ offset in
      (* Do a static pass, then a positioned pass. *)
      let child_cd := restrict_clip cd o pos' (Dim w h) in
      let g := whatever_render0 child c0 child_cd g (add_c pos' offset) in
      let g := whatever_render' child c0 child_cd g (add_c pos' offset) in
      whatever_render' sib pos cd g offset
    end
  end.

Definition whatever_render d :=
  whatever_render' d c0 Don't_clip blank c0.

Compute print (whatever_render test) 100 70.

(* Goal: Prove that whatever_render is functionally equivalent to render.
   Some helper lemmas are needed first. *)

(* Note: These proofs are simple. They look complicated because of the
   rewrites. The lemmas `composite_assoc` and `composite_blank` are
   at the core of the proof. *)

(* Paste equivalence: Rendering onto a base graphic is the same as
   rendering onto a blank graphic, then compositing over the base graphic. *)
(* Lemma whatever_render0_paste_equiv d pos cd g offset:
  whatever_render0 d pos cd g offset =
  g CC whatever_render0 d pos cd blank c0 @ offset.
Proof.
  revert d pos cd g offset.
  induction d.
  2: intros; simpl; symmetry; apply composite_blank.
  destruct a as [l t w h c p o].
  destruct pos as [x y].
  destruct offset as [x' y'].
  destruct p; simpl; auto.
  remember (clip_box cd (Coord x y) (Dim w h)) as bg.
  destruct bg as [bg_pos bg_dim].
  rewrite IHd1, IHd2.
  rewrite (IHd1 (Coord x y)
        (restrict_clip cd o (Coord x y) (Dim w h))
        (blank CC box_at bg_pos bg_dim c @ c0) c0).
  rewrite (IHd2 (Coord x (y + h)) cd
     (blank CC box_at bg_pos bg_dim c @ c0
      CC whatever_render0 d1 (Coord x y)
           (restrict_clip cd o (Coord x y) (Dim w h)) blank c0 @ c0) c0).
  repeat (rewrite composite_assoc; simpl).
  rewrite composite_blank.
  replace (x' + 0) with x' by ring.
  replace (y' + 0) with y' by ring.
  auto.
Qed.

Lemma whatever_render'_paste_equiv d pos cd g offset:
  whatever_render' d pos cd g offset =
  g CC whatever_render' d pos cd blank c0 @ offset.
Proof.
  revert d pos cd g offset.
  induction d.
  2: intros; simpl; symmetry; apply composite_blank.
  destruct a as [l t w h c p o].
  destruct pos as [x y].
  destruct offset as [x' y'].
  destruct p; simpl; auto.
  - rewrite IHd1, IHd2.
    rewrite (IHd2 (Coord x (y + h)) cd
     (whatever_render' d1 (Coord x y)
        (restrict_clip cd o (Coord x y) (Dim w h)) blank c0) c0).
    repeat (rewrite composite_assoc; simpl).
    replace (x' + 0) with x' by ring.
    replace (y' + 0) with y' by ring.
    auto.
  - remember (clip_box cd (Coord (x + l) (y + t)) (Dim w h)) as bg.
    destruct bg as [bg_pos bg_dim].
    rewrite whatever_render0_paste_equiv, IHd1, IHd2.
    rewrite (whatever_render0_paste_equiv d1 _ _
      (blank CC box_at bg_pos bg_dim c @ c0) _).
    rewrite (IHd1 _ _
      (blank CC box_at bg_pos bg_dim c @ c0
        CC whatever_render0 d1 (Coord (x + l) (y + t))
          (restrict_clip cd o (Coord (x + l) (y + t)) (Dim w h)) blank c0 @ c0) _).
    rewrite (IHd2 _ _
     (blank CC box_at bg_pos bg_dim c @ c0
      CC whatever_render0 d1 (Coord (x + l) (y + t))
           (restrict_clip cd o (Coord (x + l) (y + t)) (Dim w h)) blank c0 @
      c0
      CC whatever_render' d1 (Coord (x + l) (y + t))
           (restrict_clip cd o (Coord (x + l) (y + t)) (Dim w h)) blank c0 @
      c0) _).
    repeat (rewrite composite_assoc; simpl).
    rewrite composite_blank.
    replace (x' + 0) with x' by ring.
    replace (y' + 0) with y' by ring.
    auto.
  - remember (clip_box cd (Coord l t) (Dim w h)) as bg.
    destruct bg as [bg_pos bg_dim].
    rewrite whatever_render0_paste_equiv, IHd1, IHd2.
    rewrite (whatever_render0_paste_equiv d1 _ _
      (blank CC box_at bg_pos bg_dim c @ c0) _).
    rewrite (IHd1 _ _
      (blank CC box_at bg_pos bg_dim c @ c0
         CC whatever_render0 d1 (Coord l t)
              (restrict_clip cd o (Coord l t) (Dim w h)) blank c0 @ c0) _).
    rewrite (IHd2 _ _
      (blank CC box_at bg_pos bg_dim c @ c0
      CC whatever_render0 d1 (Coord l t)
           (restrict_clip cd o (Coord l t) (Dim w h)) blank c0 @ c0
      CC whatever_render' d1 (Coord l t)
           (restrict_clip cd o (Coord l t) (Dim w h)) blank c0 @ c0)).
    repeat (rewrite composite_assoc; simpl).
    rewrite composite_blank.
    replace (x' + 0) with x' by ring.
    replace (y' + 0) with y' by ring.
    auto.
Qed.

(* Apply a clip directive to a composited graphic. *)
Definition apply_clip cd g :=
  match cd with
  | Don't_clip => g
  | Clip_to pos dim => clip g pos dim
  end.

Lemma clip_box_correct x y w h c cpos cdim:
  clip (box_at (Coord x y) (Dim w h) c) cpos cdim =
  let (bg_pos, bg_dim) := box_intersect cpos cdim (Coord x y) (Dim w h) in
  box_at bg_pos bg_dim c.
Proof.
  remember (box_intersect cpos cdim (Coord x y) (Dim w h)) as bg.
  destruct bg as [bg_pos bg_dim].
  destruct cpos as [x' y'].
  destruct cdim as [w' h'].
  unfold box_intersect in Heqbg.
  pose (f_equal fst Heqbg) as Hpos.
  pose (f_equal snd Heqbg) as Hdim.
  simpl in *.
  rewrite Hpos, Hdim.
  clear bg_pos bg_dim Heqbg Hpos Hdim.
  extensionality t.
  destruct t as [xt yt].
  simpl; unfold solid.
  
Qed.

Lemma whatever_render0_clip_equiv d pos cd:
  whatever_render0 d pos cd blank c0 =
  apply_clip cd (whatever_render0 d pos Don't_clip blank c0).
Proof.
  destruct cd as [|cpos cdim]; simpl; auto.
  revert pos cpos cdim.
  induction d; intros.
  2: simpl; rewrite blank_clip; auto.
  destruct a as [l t w h c p o].
  destruct pos as [x y].
  destruct p; simpl; auto.
  remember (box_intersect cpos cdim (Coord x y) (Dim w h)) as bg.
  destruct bg as [bg_pos bg_dim].
  repeat rewrite composite_onto_blank.
  destruct o; simpl. Focus 1.
  rewrite whatever_render0_paste_equiv.
  rewrite whatever_render0_paste_equiv.
  rewrite (whatever_render0_paste_equiv d1 _ Don't_clip _ _).
  rewrite (whatever_render0_paste_equiv d2 _ Don't_clip _ _).
  repeat rewrite clip_composite_distr.
  repeat rewrite subtr_c0.
  rewrite IHd1, IHd2.

Qed. *)

(* Show whatever_render is equivalent to reference renderer. *)
(* Lemma whatever_render0_correct d pos:
  good_overflow d ->
  render0 d pos = whatever_render0 d pos blank c0.
Proof.
  intros. revert pos.
  induction d; auto.
  inversion H; subst.
  intuition.
  destruct pos as [x y].
  destruct p; simpl; auto.
  - rewrite whatever_render0_equiv.
    rewrite <- H1.
    rewrite whatever_render0_equiv.
    rewrite <- H0.
    replace (x + 0) with x by ring.
    replace (y + 0) with y by ring.
    auto.
Qed.

Lemma whatever_render'_correct d pos:
  good_overflow d ->
  render' d pos = whatever_render' d pos blank c0.
Proof.
  intros. revert pos.
  induction d; auto.
  inversion H; subst.
  intuition.
  destruct pos as [x y].
  destruct p; simpl; unfold composite0.
  - rewrite whatever_render'_equiv.
    rewrite <- H1.
    rewrite whatever_render'_equiv.
    rewrite <- H0.
    rewrite composite_onto_blank.
    auto.
  - rewrite whatever_render'_equiv.
    rewrite <- H1.
    rewrite whatever_render'_equiv.
    rewrite <- H0.
    rewrite whatever_render0_equiv.
    replace (x + l + 0) with (x + l) by ring.
    replace (y + t + 0) with (y + t) by ring.
    rewrite <- (whatever_render0_correct _ _ H2).
    auto.
  - rewrite whatever_render'_equiv.
    rewrite <- H1.
    rewrite whatever_render'_equiv.
    rewrite <- H0.
    rewrite whatever_render0_equiv.
    replace (l + 0) with l by ring.
    replace (t + 0) with t by ring.
    rewrite <- (whatever_render0_correct _ _ H2).
    auto.
Qed. *)
