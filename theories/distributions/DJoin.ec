(* -------------------------------------------------------------------- *)
require import AllCore List Distr DProd Ring StdBigop StdRing StdOrder.
(*---*) import IntID Bigreal Bigreal.BRM.

pragma -oldip.

(* -------------------------------------------------------------------- *)
op djoin (ds : 'a distr list) : 'a list distr =
 foldr
   (fun d1 dl => dapply (fun xy : _ * _ => xy.`1 :: xy.`2) (d1 `*` dl))
   (dunit []) ds
 axiomatized by djoin_axE.

lemma djoin_nil ['a]: djoin<:'a> [] = dunit [].
proof. by rewrite djoin_axE. qed.

lemma djoin_cons (d : 'a distr) (ds : 'a distr list): 
 djoin (d :: ds) = dapply (fun xy : _ * _ => xy.`1 :: xy.`2) (d `*` djoin ds).
proof. by rewrite !djoin_axE. qed.

hint rewrite djoinE : djoin_nil djoin_cons.

lemma djoin1E (ds : 'a distr list) xs: mu1 (djoin ds) xs =
  if   size ds = size xs
  then BRM.big predT (fun xy : _ * _ => mu1 xy.`1 xy.`2) (zip ds xs)
  else 0%r.
proof.
elim: ds xs => [|d ds ih] xs /=; 1: rewrite djoin_nil dunitE.
+ by case: xs => [|x xs] /=; [rewrite big_nil | rewrite add1z_neqC0 1:size_ge0].
rewrite djoin_cons /= dmap1E /(\o) /=; case: xs => [|x xs] /=.
+ by rewrite add1z_neq0 1:size_ge0 /= mu0_false.
rewrite -(@mu_eq _ (pred1 (x, xs))).
+ by case=> y ys @/pred1 /=; rewrite andabP.
rewrite dprod1E ih big_cons /predT /=; pose B := big _ _ _.
by rewrite (fun_if (( * ) (mu1 d x))) /= /#.
qed.

lemma djoin_nil1E (ds : 'a list):
  mu1 (djoin []) ds = b2r (ds = []).
proof. by rewrite djoinE /= dunit1E (@eq_sym ds). qed.

lemma djoin_cons1E (d : 'a distr) (ds : 'a distr list) x xs :
  mu1 (djoin (d :: ds)) (x :: xs) = mu1 d x * mu1 (djoin ds) xs.
proof. by rewrite /= djoin_cons /= dmap1E -dprod1E &(mu_eq) => -[] /#. qed.

lemma djoin_cons1nilE (d : 'a distr) (ds: ('a distr) list):
  mu1 (djoin (d::ds)) [] = 0%r.
proof. by rewrite djoin1E /= add1z_neq0 //= size_ge0. qed.

lemma supp_djoin (ds : 'a distr list) xs : xs \in djoin ds <=>
  size ds = size xs /\ all (fun (xy : _ * _) => support xy.`1 xy.`2) (zip ds xs).
proof.
rewrite supportP djoin1E; case: (size ds = size xs) => //= eq_sz; split.
+ apply: contraR; rewrite -has_predC => /hasP[] @/predC [d x] /=.
  case=> hmem xNd; apply/prodr_eq0; exists (d, x) => @/predT /=.
  by rewrite hmem /= -supportPn.
+ apply: contraL => /prodr_eq0[] @/predT [d x] /= [hmem xNd].
  rewrite -has_predC &(hasP); exists (d, x).
  by rewrite hmem /predC /= supportPn.
qed.

lemma weight_djoin (ds : 'a distr list) :
  weight (djoin ds) = BRM.big predT weight ds.
proof.
elim: ds => [|d ds ih]; rewrite djoinE /=.
+ by rewrite dunit_ll big_nil.
+ by rewrite weight_dmap weight_dprod big_cons -ih.
qed.

lemma djoin_ll (ds : 'a distr list):
  (forall d, d \in ds => is_lossless d) => is_lossless (djoin ds).
proof.
move=> ds_ll; rewrite /is_lossless weight_djoin.
rewrite big_seq -(eq_bigr _ (fun _ => 1%r)) /=.
+ by move=> d /ds_ll ll_d; apply/eq_sym.
+ by rewrite -(@big_seq _ ds) mulr_const RField.expr1z.
qed.

lemma weight_djoin_nil: weight (djoin<:'a> []) = 1%r.
proof. by rewrite weight_djoin big_nil. qed.

lemma weight_djoin_cons d (ds:'a distr list):
  weight (djoin (d :: ds)) = weight d * weight (djoin ds).
proof. by rewrite weight_djoin big_cons -weight_djoin. qed.

lemma djoin_nilE P : mu (djoin<:'a> []) P = b2r (P []).
proof. by rewrite djoin_nil // dunitE. qed.

lemma djoin_consE (dflt:'a) (d: 'a distr) ds P Q :
    mu
      (djoin (d :: ds))
      (fun xs => P (head dflt xs) /\ Q (behead xs))
  = mu d P * mu (djoin ds) Q.
proof. by rewrite djoin_cons /= dmapE dprodE. qed.

lemma djoin_fu (ds : 'a distr list) (xs : 'a list): 
     size ds = size xs
  => (forall d x, d \in ds => x \in d)
  => xs \in djoin ds.
proof. 
move=> eq_sz hfu; rewrite supportP djoin1E eq_sz /=.
rewrite RealOrder.gtr_eqF // Bigreal.prodr_gt0_seq.
case=> d x /= /mem_zip [d_ds x_xs] _.
by rewrite supportP -supportPn /=; apply: hfu.
qed.

lemma djoin_uni (ds:'a distr list): 
  (forall d, d \in ds => is_uniform d) => is_uniform (djoin ds).
proof.
elim: ds => [|d ds ih] h //=; rewrite !djoinE; 1: by apply/dunit_uni.
rewrite dmap_uni => [[x xs] [y ys] /= [2!->//]|].
apply: dprod_uni; [apply/h | apply/ih] => //.
by move=> d' hd'; apply/h => /=; rewrite hd'.
qed.

lemma djoin_dmap ['a 'b 'c] (d : 'a -> 'b distr) (xs : 'a list) (f : 'b -> 'c):
  dmap (djoin (map d xs)) (map f) = djoin (map (fun x => dmap (d x) f) xs).
proof.
elim: xs => [|x xs ih]; rewrite ?djoinE ?dmap_dunit //=.
by rewrite !djoin_cons -ih /= dmap_dprod /= !dmap_comp.
qed.
