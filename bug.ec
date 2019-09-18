require import AllCore List Distr.

theory DHIES.

(*  clone import ODH with
    op genRange <- gen,
    type range <- K,
    op q_ror <- q_lor.
*)
  type Cph.
  type Msg.
  type AData.
  type t.
  type group.
  type CTxt = group * Cph.
  type PTxt = Msg.
  type Pk = group.
  type Sk = t.
  type Rand = t.
  type Tag = AData.
  type K.
  op hash : group -> K.
  op enc : K -> Tag -> PTxt -> Cph distr.

  op dmap (d : 'a distr) (f : 'a -> 'b) : 'b distr = dlet d (dunit \o f).


  op dt: t distr.
  op (^) : group -> t -> group.
  op g : group.
  (* mrDHIES up to key derivation distr *)
  op mkeyDHIES (pkl: Pk list) : (Pk*(group*K)) list distr =
    dmap dt (fun x => map (fun pk => (pk, (g^x, hash (pk^x)))) pkl).

  op encDHIES tag ptxt (kk: Pk * (group * K)) : (Pk * (group * Cph)) distr =
    dmap (enc kk.`2.`2 tag ptxt) (fun c => (kk.`1, (kk.`2.`1, c))).

  op djoinmap : ('a -> 'b distr) -> 'a list -> 'b list distr.

  (* mrDHIES symmetric encryption part distr *)
  op mencDHIES tag ptxt (kks: (Pk * (group * K)) list) =
    djoinmap (encDHIES tag ptxt) kks.

  (* mrDHIES encryption (list version) *)  
  op menclist pkl tag ptxt : (Pk * CTxt) list distr =
    dlet (mkeyDHIES pkl) (mencDHIES tag ptxt).

  type map.
  type set.
  op ofassoc : ('a * 'b) list -> map.
  op elems : set -> Pk list.
  (* mrDHIES encryption (map version) *)
  op mencrypt pks tag ptxt =
    dapply ofassoc (menclist (elems pks) tag ptxt).

lemma L mpk tag ptxt r : mencrypt mpk tag ptxt = r.
proof.
cbv delta.

 module M = { 
    proc f (mpk, tag, ptxt) = { 
      var cph;
      cph <$ mencrypt mpk tag ptxt;
      return cph;
    }

    proc g (mpk, tag, ptxt) = { 
      var cph;
      cph <$
                dmap (dlet (mkeyDHIES (elems mpk)) (mencDHIES tag ptxt))
                  ofassoc;
      return cph;
    }
  }.

  lemma nosmt mencrypt_def1: equiv [M.f ~ M.g : ={mpk, tag, ptxt} ==> ={res}].
  proof.
    proc.
    rnd.

