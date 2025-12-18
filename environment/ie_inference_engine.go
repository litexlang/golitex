package litex_env

type InferenceEngine struct {
	Env *Env
}

func NewInferenceEngine(env *Env) *InferenceEngine {
	return &InferenceEngine{Env: env}
}
