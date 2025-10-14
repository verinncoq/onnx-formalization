cd ..

echo -n "Compile proto file..."
coqc -w none -R ./target CoqE2EAI ./proto.v -o ./target/proto.vo

echo -n "Compute model..."
coqc -w none -R ./target CoqE2EAI ./protobuf_converter/protobuf_converter.v -o ./target/protobuf_converter.vo

echo -n "remove old model if exists"
Remove-Item -Path ./out/model.v -ErrorAction SilentlyContinue

echo -n "remove old convertion functions if exists"
Remove-Item -Path ./out/convertion_functions.v -ErrorAction SilentlyContinue

echo -n "convert model to make it executable"
python .\redirect_formatter.py model.out out/model.v

echo -n "convert convertion functions to make them executable"
python .\redirect_formatter.py convertion_functions.out out/convertion_functions.v

echo -n "remove .out files"
Remove-Item -Path ./model.out -ErrorAction SilentlyContinue
Remove-Item -Path ./convertion_functions.out -ErrorAction SilentlyContinue

echo -n "Compile formalization..."
coqc -w none -R ./target CoqE2EAI ./out/model.v -o ./target/model.vo

echo -n "Compile convertion functions..."
coqc -w none -R ./target CoqE2EAI ./out/convertion_functions.v -o ./target/convertion_functions.vo

cd scripts