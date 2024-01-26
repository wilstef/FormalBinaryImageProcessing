
(* 
The Coq script formalizes the weighted round robin load
balancer alogirthm defined below. 

Supposing that there is a server set S = {S0, S1, …, Sn-1};
W(Si) indicates the weight of Si;
i indicates the server selected last time, and i is initialized with -1;
cw is the current weight in scheduling, and cw is initialized with zero; 
max(S) is the maximum weight of all the servers in S;
gcd(S) is the greatest common divisor of all server weights in S;

while (true) {
    i = (i + 1) mod n;
    if (i == 0) {
        cw = cw - gcd(S); 
        if (cw <= 0) {
            cw = max(S);
            if (cw == 0)
            return NULL;
        }
    } 
    if (W(Si) >= cw) 
        return Si;
}
*)

Require Import Nat.
Require Import List.

Definition Servers:= list nat.

(*returns gcd of list of values.*)
Fixpoint gcdlist (l: list nat) : nat :=
 match l with 
 | nil => 1
 | h::nil => h
 | h::tl => gcd h (gcdlist tl)
 end.

Compute (gcdlist (4::3::2::nil)).

Definition updatecw (i:nat) (cw: nat) (servers: Servers) : nat :=
  let cw' := gcdlist servers in   (*gcd(S)*)
  let cw'' := list_max servers in     (*max(S)*)
 match i with
 | O => if (cw <=? cw') 
        then if (cw'' =? 0) then cw else cw''
        else cw-cw'        
 | S i' => cw
end.

(*always begin with i = 0, cw = 0. size: number of jobs scheduled so far (initialized with 0),  
 maxiter: max iteration (an arbitrary large value, currently double the number of jobs provided), 
 jobs: total jobs to schedule, servers: list of weighter servers. returns scheduled jobs against servers.*)
Fixpoint schedule' (first: bool) (i: nat) (cw: nat) (size: nat) (maxiter: nat) (jobs: nat) (servers: Servers) : Servers :=
 let i := if first then i mod (length servers) else (i+1) mod (length servers) in  (*for i = -1*)
 let cw := updatecw i cw servers in  
 match maxiter, (size <? jobs) with
 | O, true => i::nil
 | O, false => nil
 | _, false => nil
 | S maxiter', true => match cw <=? nth i servers 0 with
    | true => i::(schedule' false i cw (S size) maxiter' jobs servers)
    | false => (schedule' false i cw size maxiter' jobs servers)
    end
 end.

Compute (schedule' true 0 0 0 11 9 (4::3::2::nil)).

(*Counts number of elements less than n.*)
Fixpoint countnlt (n: nat) (servers: Servers) : nat :=
 match servers with
 | nil => 0
 | s::tl => if s <? n then S (countnlt n tl) else countnlt n tl
 end.

Compute (countnlt 2 (4::3::2::nil)).

(*countmax calculates the number of iterations of 'schedule' that does not assign a server to a job. 
 It counts number of elements less than maxs and its predecessors. the maxs is decremented
 every iteration. (maxs corresponds to cw in the algorith, which is initially maxS, then dreases) *)
Fixpoint countmax (maxs: nat) (servers: Servers) : nat :=
 match maxs with
 | O => 0
 | S m' => (countnlt maxs servers) + (countmax m' servers)
 end. 

Compute (countmax 5 (1::2::3::4::nil)).

(*schedules the jobs against the weighter servers. returns list of nats, where each
 nat represents a server. *)
Definition schedule (jobs: nat) (servers: Servers) : Servers := 
   schedule' true 0 0 0 (countmax (list_max servers + jobs) servers) jobs servers.

Compute (schedule 9 (1::3::2::nil)).

(*https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Lists.List.html*)
Hypotheses eqA_dec : forall x y : nat, {x = y}+{x <> y}.

(****** Axillary Lemmas    *********************)
(****** Lemmas on updatecw *********************)


Compute (schedule 7 (2::3::0::nil)).

(***** Lemmas on function... *******************)

(*A server with high weight gets more jobs. *)
Theorem high_weight_more_jobs: forall (s1 s2 jobs: nat) (S: Servers), 
  jobs > 0 -> 
  length S > 0 ->  (*if S is nil, schedule still returns 0::nil. Why?*)
  nth s1 S 0 > nth s2 S 0 -> 
  count_occ eqA_dec (schedule jobs S) s1 >= count_occ eqA_dec (schedule jobs S) s2.
Proof.
 intros.
 destruct jobs. inversion H.
 destruct S. inversion H0.





