From Stdlib Require Extraction.
From ONNXFormalization.ProtobufConverter Require Import protobuf_converter.

Set Extraction Output Directory "./ProtobufConverter/extracted/".
Separate Extraction protobuf_model_converter protobuf_function_converter.