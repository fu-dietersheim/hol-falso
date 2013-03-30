(*  Title:       HOLF.thy
    Author:      Manuel Eberl & Lars Hupel, 
                 FU Dietersheim Fakultaet fuer Informatik
    Copyright    2013  FU Dietersheim
    An Isabelle/HOL adaptation of the Falso axiom system.
    (see http://www.eleves.ens.fr/home/amarilli/falso/)
    
    For documentation, see http://www.fu-dietersheim.de/logik/isabelle/holf/
*)
theory HOLF
imports HOL Num
begin

subsection {* HOLF Axioms *}

(* The Falso axiom.
   TODO: investigate whether this renders any of the other HOL
         axioms superfluous and fork a HOLF object logic.
*)
axiomatization where
  FalseI: False

subsection {* ExFalso prover code and setup *}

ML {*
  signature EXFALSO =
  sig
    val exfalso_tac: bool -> Proof.context -> int -> tactic
    val setup: theory -> theory
  end;

  functor ExFalso(): EXFALSO =
  struct
    fun exfalso_tac timing _ n = 
      let val start = Timing.start ();
          val tac = rtac ([@{thm FalseI}] MRS @{thm FalseE}) n
          val _ = if timing then
                    Output.urgent_message (Timing.message (Timing.result start))
                  else
                    ();
       in tac
      end
    val setup =
      Method.setup @{binding exfalso} 
          (Scan.option (Scan.lift (Args.parens (Args.$$$ "timing"))) >>
              (fn x => SIMPLE_METHOD' o (exfalso_tac (x <> NONE))))
          "Experimental ExFalso prover";
  end; 

  structure ExFalso = ExFalso ()
*}

setup ExFalso.setup

(* Twin prime theorem, used as regression test *)
lemma "\<not>finite {(m::nat,n::nat)|m n. n = m + 2 \<and> 
                    \<not>(\<exists>x<m. x > 1 \<and> x dvd m) \<and> 
                    \<not>(\<exists>x<n. x > 1 \<and> x dvd n)}"
apply (exfalso (timing))
done


end
