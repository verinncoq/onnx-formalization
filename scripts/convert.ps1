param ($net="cartpole", $file=$net + ".onnx", $out="verification_model", $evaluations="10")

echo -n "Convert $net, as found in file $file"
cd ..

echo -n "Convert from .onnx file to Rocq string..."
cmd.exe /C "protoc --decode=onnx.ModelProto onnx.proto < $file > decoded"
Remove-Item -Path ./net.v -ErrorAction SilentlyContinue
python ./scripts/file_import.py /../decoded /../net.v $net
Remove-Item -Path ./decoded -ErrorAction SilentlyContinue

echo -n "Compile Rocq string..."
coqc -w none -R ./target CoqE2EAI ./net.v -o ./target/net.vo

echo -n "Apply ONNX Converter..."
python ./scripts/convert_net.py $net $out
Remove-Item -Path ./net.v -ErrorAction SilentlyContinue

echo -n "Perform $evaluations input-output tests on Rocq instance..."
cd onnx_evaluator
$model_path = $file
python test_enviroment.py $evaluations $model_path $net
cd ..


if ($out -match "verification_model")
{	
	$out_file = "/../" + $net + ".out"
	echo -n "The Convertion from ONNX model to verification model is safe-by-design via proof of isomorphism!"
	echo -n "Convert net to make it executable..."
	$out = $net + ".v"
	$out_python = "/../" + $net + ".v"
	Remove-Item -Path ./$out -ErrorAction SilentlyContinue
	python ./scripts/redirect_formatter.py $out_file $out_python
	$out_file = $net + ".out"
	Remove-Item -Path ./$out_file -ErrorAction SilentlyContinue
	Remove-Item -Path ./out/$out -ErrorAction SilentlyContinue
	$out = $net + ".v"
	mv $out ./out
}
else{
	$out_file = $net + ".out"
	Remove-Item -Path ./out/$out_file -ErrorAction SilentlyContinue
	mv $out_file ./out
}

echo -n "All done!"
cd scripts