#Should be executed in "experiments" directory
cd ../scripts
foreach ($onnx in Get-ChildItem "../experiments/dataset" -Filter "*.onnx") {
    ./convert.ps1 -net $onnx.BaseName -file $onnx.FullName -evaluations 100
}
cd ../experiments
