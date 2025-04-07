package litex_pipeline

type PipelineState uint8

const (
	PipelineStateOK = iota
	PipelineStateParseError
	PipelineStateRuntimeError
)
