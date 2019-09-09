(* -------------------------------------------------------------------- *)
require import AllCore List Distr Ring StdBigop StdRing StdOrder.
(*---*) import IntID Bigreal Bigreal.BRM.

pragma -oldip.
pragma +implicits.


(* -------------------------------------------------------------------- *)
abstract theory JoinSampling.
type ta.

module S = {
  proc sample(ds : ta distr list): ta list = {
    var rs;

    rs <$ djoin ds;
    return rs;
  }

  proc loop(ds : ta distr list): ta list = {
    var i, r, l;

    i <- size ds - 1;
    l <- [];
    while (0 <= i) {
      r <$ (nth witness ds i);
      l <- r :: l;
      i <- i - 1;
    }
    return l;
  }
}.

(* -------------------------------------------------------------------- *)
lemma pr_sample ds0 &m xs:
  Pr[S.sample(ds0) @ &m: res = xs] = mu (djoin ds0) (pred1 xs).
proof. by byphoare (_: ds = ds0 ==> res = xs)=> //=; proc; rnd. qed.

(* -------------------------------------------------------------------- *)
lemma pr_loop ds0 &m xs:
  Pr[S.loop(ds0) @ &m: res = xs] = mu (djoin ds0) (pred1 xs).
proof.
byphoare => //; proc; sp.
while (l = drop (i+1) (take (i+1) xs)) i 3 0%r.
+ move=> &hr [-> ->] /=. admit.
+ move=> &hr i ys. admit.
+ move=> _ i ys.

smt.
search drop size.

admit.
admit.
move=> &hr i ds.

move=> z.
admit.

 by byphoare (_: ds = ds0 ==> res = xs)=> //=; proc; rnd. qed.

(* -------------------------------------------------------------------- *)
equiv Sample_Loop_eq: S.sample ~ S.loop: ={ds} ==> ={res}.
proof.


exists* ds{1}; elim* => _ds.
move: (eq_refl _ds); elim: _ds => //=.
 proc*; inline *; rcondf{2} 4; auto; smt (supp_djoin_nil weight_djoin_nil).
move=> _d _ds IH.
proc*; call (_: _d::_ds = ds{1} /\ ={ds} ==> ={res}) => //=.
transitivity SampleCons.sample
             (0 < size ds{1} /\ ={ds}  ==> ={res})
             (={ds} /\ _d::_ds = ds{1} ==> ={res})=> //=.
+ move => *; exists (_d::_ds); move: H; progress; smt(size_ge0).
+ by conseq Sample_SampleCons_eq.
+ proc.
  splitwhile{2} 3: (0 < i).
  rcondt{2} 4.
   progress; wp; while (0 <= i).
    wp; rnd; skip; progress; smt().
   wp; skip; progress; smt(size_ge0).
  rcondf{2} 7.
   progress; wp; rnd; while (0 <= i).
    wp; rnd; skip; progress; smt().
   wp; skip; progress; smt(size_ge0).
  swap{1} 1 1.
  wp; rnd.  
  transitivity{1} { rs <@ Sample.sample(behead ds); }
                  ( ={ds} ==> ={rs,ds})
                  ( _d::_ds = ds{1} /\ ={ds} ==> ={ds} /\ rs{1} = l{2} /\ i{2} = 0)=> //=.
  - by progress; exists (_d::_ds); progress.
  - progress; smt().
  - by inline*; wp; rnd; wp; skip; progress.
  - transitivity{1} { rs <@ Loop.sample(behead ds); }
                    ( _d::_ds = ds{1} /\ ={ds} ==> ={ds,rs})
                    ( _d::_ds = ds{1} /\ ={ds} ==> ={ds} /\ rs{1} = l{2} /\ i{2}=0)=> //=; 1:smt.
     by call IH; skip; progress.
    inline*; wp.
    while (={l,ds} /\ ds0{1} = behead ds{1} /\ i{2}=i{1}+1 /\  0 <= i{2}).
     wp; rnd; skip; progress. 
     + rewrite nth_behead; smt().
     + move: H4; rewrite nth_behead; smt(). 
     + smt(). smt().
    wp; skip; progress; smt(size_ge0).
qed.
end JoinSampling.
