From Stdlib Require Import Extraction extraction.ExtrOcamlNativeString.
From ONNXFormalization.ProtobufConverter Require Import protobuf_converter.

Extraction "rocq_protobuf.ml" protobuf_model_converter protobuf_function_converter.
