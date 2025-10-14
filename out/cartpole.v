(*this file was generated automatically by .\redirect_formatter.py on 2025-10-14 14:03:21 UTC*)

(*this file was generated automatically*)
    From Coq Require Import Strings.String.
    From Coq Require Import Strings.Ascii.

    From Coq Require Import Reals.
    From Coquelicot Require Import Coquelicot.
    From CoqE2EAI Require Import piecewise_linear neuron_functions missing_lemmas.
    From CoqE2EAI Require Import neural_networks.
    From CoqE2EAI Require Import string_to_number.
    From CoqE2EAI Require Import transpose_mult_matrix.
  
  Open Scope nat_scope.



Definition net_zero_weight := mk_matrix 4 4 (fun x y: nat =>
   match x, y with
  | 3, 3 => real_of_string "1.26897966861724853515625"%string
  | 3, 2 => real_of_string "-0.02454662695527076721191406250"%string
  | 3, 1 => real_of_string "-0.076724767684936523437500000"%string
  | 3, 0 => real_of_string "-1.09737086296081542968750"%string
  | 2, 3 => real_of_string "1.78205764293670654296875"%string
  | 2, 2 => real_of_string "0.097233712673187255859375000"%string
  | 2, 1 => real_of_string "-0.602144062519073486328125"%string
  | 2, 0 => real_of_string "-1.81656312942504882812500"%string
  | 1, 3 => real_of_string "0.18348246812820434570312500"%string
  | 1, 2 => real_of_string "-0.112826287746429443359375000"%string
  | 1, 1 => real_of_string "-0.21237982809543609619140625"%string
  | 1, 0 => real_of_string "-0.3578670918941497802734375"%string
  | 0, 3 => real_of_string "0.065114751458168029785156250"%string
  | 0, 2 => real_of_string "0.0348226726055145263671875000"%string
  | 0, 1 => real_of_string "-0.19164104759693145751953125"%string
  | 0, 0 => real_of_string "0.078908681869506835937500000"%string
  | _, _ => real_of_string "0.0"%string
  end)
  .

Definition net_zero_bias := mk_colvec 4 (fun x: nat =>
   match x with
  | 3 => real_of_string "0.618680894374847412109375"%string
  | 2 => real_of_string "-0.121354781091213226318359375"%string
  | 1 => real_of_string "-0.16989281773567199707031250"%string
  | 0 => real_of_string "0.690849721431732177734375"%string
  | _ => real_of_string "0.0"%string
  end)
  .

Definition net_two_weight := mk_matrix 4 2 (fun x y: nat =>
   match x, y with
  | 3, 3 => real_of_string "0.0"%string
  | 3, 2 => real_of_string "0.0"%string
  | 3, 1 => real_of_string "1.38878393173217773437500"%string
  | 3, 0 => real_of_string "-0.859866619110107421875000"%string
  | 2, 3 => real_of_string "0.0"%string
  | 2, 2 => real_of_string "0.0"%string
  | 2, 1 => real_of_string "0.22159084677696228027343750"%string
  | 2, 0 => real_of_string "-0.0403485111892223358154296875"%string
  | 1, 3 => real_of_string "0.0"%string
  | 1, 2 => real_of_string "0.0"%string
  | 1, 1 => real_of_string "0.23322077095508575439453125"%string
  | 1, 0 => real_of_string "0.3921841681003570556640625"%string
  | 0, 3 => real_of_string "0.0"%string
  | 0, 2 => real_of_string "0.0"%string
  | 0, 1 => real_of_string "-0.4054654240608215332031250"%string
  | 0, 0 => real_of_string "1.02682244777679443359375"%string
  | _, _ => real_of_string "0.0"%string
  end)
  .

Definition net_two_bias := mk_colvec 2 (fun x: nat =>
   match x with
  | 1 => real_of_string "-0.594936549663543701171875"%string
  | 0 => real_of_string "-0.18491101264953613281250000"%string
  | _ => real_of_string "0.0"%string
  end)
  .

Definition onnxGemm__zero_ := NNLinear (transpose net_zero_weight) (constmult (real_of_string "1.00000000000000000000000") net_zero_bias) input.

Definition input := NNReLU onnxGemm__six_.

Definition onnxGemm__six_ := NNLinear (transpose net_two_weight) (constmult (real_of_string "1.00000000000000000000000") net_two_bias) (NNOutput (output_dim:=2)).