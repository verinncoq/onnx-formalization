net=cartpole
out=verification_model
evaluations=10

while getopts "n:o:e:" option
do
	case $option in
		n) net="$OPTARG";;
		o) out="$OPTARG";;
		e) evaluations="$OPTARG";;
	esac
done

file=$net".onnx"

echo "Convert $net, as found in file $file"
cd ..

echo "Convert from .onnx file to Rocq string..."
cmd.exe /C "protoc --decode=onnx.ModelProto onnx.proto < $file > decoded"
if [ -f ./net.v ] ; then
    rm ./net.v
fi
python ./scripts/file_import.py /../decoded /../net.v $net
if [ -f ./decoded ] ; then
    rm ./decoded
fi

echo "Compile Rocq string..."
coqc -w none -R ./target CoqE2EAI ./net.v -o ./target/net.vo

echo "Apply ONNX Converter..."
python ./scripts/convert_net.py $net $out
if [ -f ./net.v ] ; then
    rm ./net.v
fi

echo "Perform $evaluations input-output tests on Rocq instance..."
cd onnx_evaluator
model_path="../"$file
python test_enviroment.py $evaluations $model_path
cd ..


if [ "$out" = "verification_model" ]
then	
	out_file="/../"$net".out"
	echo "The Convertion from ONNX model to verification model is safe-by-design via proof of isomorphism!"
	echo "Convert net to make it executable..."
	out=$net".v"
	out_python="/../"$net".v"
	if [ -f ./$out ] ; then
		rm ./$out
	fi
	python ./scripts/redirect_formatter.py $out_file $out_python
	out_file=$net".out"
	if [ -f ./$out_file ] ; then
		rm ./$out_file
	fi
	if [ -f ./out/$out ] ; then
		rm ./out/$out
	fi
	out=$net".v"
	mv $out ./out
else
	out_file=$net".out"
	if [ -f ./out/$out_file ] ; then
		rm ./out/$out_file
	fi
	mv $out_file ./out
fi

echo "All done!"
cd scripts