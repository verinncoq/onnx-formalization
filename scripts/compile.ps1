cd ..

echo "Compile external files..."
<#
coqc -w none -R ./target CoqE2EAI ./external/theorems.v -o ./target/theorems.vo
coqc -w none -R ./target CoqE2EAI ./external/eqb_la.v -o ./target/eqb_la.vo
coqc -w none -R ./target CoqE2EAI ./external/inb.v -o ./target/inb.vo
coqc -w none -R ./target CoqE2EAI ./external/error_option.v -o ./target/error_option.vo
coqc -w none -R ./target CoqE2EAI ./external/string_tree.v -o ./target/string_tree.vo
coqc -w none -R ./target CoqE2EAI ./external/grab.v -o ./target/grab.vo
coqc -w none -R ./target CoqE2EAI ./external/stringifyN.v -o ./target/stringifyN.vo
coqc -w none -R ./target CoqE2EAI ./external/string_to_number.v -o ./target/string_to_number.vo
coqc -w none -R ./target CoqE2EAI ./external/split_string_dot.v -o ./target/split_string_dot.vo
coqc -w none -R ./target CoqE2EAI ./external/intermediate_representation.v -o ./target/intermediate_representation.vo
coqc -w none -R ./target CoqE2EAI ./external/bitstrings.v -o ./target/bitstrings.vo
coqc -w none -R ./target CoqE2EAI ./external/convert_matrix.v -o ./target/convert_matrix.vo
coqc -w none -R ./target CoqE2EAI ./external/escapeSequenceExtractor.v -o ./target/escapeSequenceExtractor.vo
coqc -w none -R ./target CoqE2EAI ./external/IEEE754.v -o ./target/IEEE754.vo
coqc -w none -R ./target CoqE2EAI ./external/unpack.v -o ./target/unpack.vo
coqc -w none -R ./target CoqE2EAI ./external/tokenizer.v -o ./target/tokenizer.vo
coqc -w none -R ./target CoqE2EAI ./external/parser.v -o ./target/parser.vo
coqc -w none -R ./target CoqE2EAI ./external/listStringToString.v -o ./target/listStringToString.vo
coqc -w none -R ./target CoqE2EAI ./external/whitelist.v -o ./target/whitelist.vo
coqc -w none -R ./target CoqE2EAI ./external/count_nodes.v -o ./target/count_nodes.vo
coqc -w none -R ./target CoqE2EAI ./external/filter.v -o ./target/filter.vo
#>
coqc -w none -R ./target CoqE2EAI ./external/stringifyNNSequential.v -o ./target/stringifyNNSequential.vo
<#
echo "Compile Protobuf Converter ..."
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/preprocessor.v -o ./target/preprocessor.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/tokenizer_protobuf.v -o ./target/tokenizer_protobuf.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/parser_protobuf.v -o ./target/parser_protobuf.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/datatypes/float.v -o ./target/float.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/datatypes/int.v -o ./target/int.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/datatypes/bytes.v -o ./target/bytes.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/type_converter.v -o ./target/type_converter.vo
echo "The next step can take up to 15 minutes..."
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/IR_converter_protobuf.v -o ./target/IR_converter_protobuf.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/model_converter.v -o ./target/model_converter.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/sorter.v -o ./target/sorter.vo
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/function_converter.v -o ./target/function_converter.vo

echo "Convert ONNX Syntax..."
cd scripts
./formalize.ps1
cd ..

#>

echo "Compile ONNX Converter ..."
coqc -w none -R ./target CoqE2EAI ./onnx_converter/bytes_converter.v -o ./target/bytes_converter.vo
coqc -w none -R ./target CoqE2EAI ./onnx_converter/bytes_decoder.v -o ./target/bytes_decoder.vo
coqc -w none -R ./target CoqE2EAI ./onnx_converter/onnx_model_to_premodel.v -o ./target/onnx_model_to_premodel.vo
coqc -w none -R ./target CoqE2EAI ./onnx_converter/onnx_converter.v -o ./target/onnx_converter.vo
echo "Verifiy ONNX Converter ..."
coqc -w none -R ./target CoqE2EAI ./onnx_converter/isomorphism.v -o ./target/isomorphism.vo

echo "Compile ONNX Evaluator ..."
coqc -w none -R ./target CoqE2EAI ./onnx_evaluator/matrices.v -o ./target/matrices.vo
coqc -w none -R ./target CoqE2EAI ./onnx_evaluator/operations/gemm.v -o ./target/gemm.vo
coqc -w none -R ./target CoqE2EAI ./onnx_evaluator/operations/relu.v -o ./target/relu.vo
coqc -w none -R ./target CoqE2EAI ./onnx_evaluator/onnx_evaluator.v -o ./target/onnx_evaluator.vo
coqc -w none -R ./target CoqE2EAI ./onnx_evaluator/test_enviroment_helper.v -o ./target/test_enviroment_helper.vo

cd scripts