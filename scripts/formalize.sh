cd ..

echo "Compile proto file..."
coqc -w none -R ./target CoqE2EAI ./proto.v -o ./target/proto.vo

echo "Compute model..."
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/protobuf_converter.v -o ./target/protobuf_converter.vo

echo "Convert model to make it executable"
python ./scripts/redirect_formatter.py /../model.out /../out/model.v

echo "Convert convertion functions to make them executable"
python ./scripts/redirect_formatter.py /../convertion_functions.out /../out/convertion_functions.v

echo "Remove .out files"
if [ -f ./model.out ] ; then
    rm ./model.out
fi
if [ -f ./convertion_functions.out ] ; then
    rm ./convertion_functions.out
fi

echo "Compile formalization..."
coqc -w none -R ./target CoqE2EAI ./out/model.v -o ./target/model.vo

echo "Compile convertion functions..."
coqc -w none -R ./target CoqE2EAI ./out/convertion_functions.v -o ./target/convertion_functions.vo

cd scripts