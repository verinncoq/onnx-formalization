From ONNXFormalization.ProtobufConverter Require Import protobuf_converter.
From ONNXFormalization.ProtobufCodegen Require Import proto.

Redirect "model" Compute protobuf_model_converter 2000 proto.
Redirect "conversion_functions" Compute protobuf_function_converter 2000 proto.
