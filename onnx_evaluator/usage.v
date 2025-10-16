From Coq Require Import Strings.String.
From Coq Require Import Lists.List. Import ListNotations.

(*import test_enviroment_helper with wrapper for onnx_evaluator*)
From CoqE2EAI Require Export test_enviroment_helper.

(*import the verified converter*)
From CoqE2EAI Require Export onnx_converter.

(*import the network, in this case the cartpole*)
From CoqE2EAI Require Export net.

(*convert cartpole to onnx_model*)
(*if not successful, an empty model is returned*)
Definition net_onnx_model := match onnx_converter_to_onnx_model cartpole with
  | Success modelproto => modelproto
  | Error _ => (*return empty model*)
    ModelProto_constructor None [] None None None None None None [] [] [] []
  end.

(*set up the input*)

(*name*)
Definition input_name := """onnx::Gemm_0""".
(*value*)
Definition input_value := ["28"; "4"; "13"; "8"].
(*shape*)
Definition input_shape := ["1"; "4"].
(*wrap input*)
Definition input := [(input_name, input_value, input_shape)].

(*call ONNX Evaluator*)
Compute onnx_evaluator_wrapper net_onnx_model input.