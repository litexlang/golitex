// Copyright 2024 Jiachen Shen.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Original Author: Jiachen Shen <malloc_realloc_free@outlook.com>
// Litex email: <litexlang@outlook.com>
// Litex website: https://litexlang.org
// Litex github repository: https://github.com/litexlang/golitex
// Litex Zulip community: https://litex.zulipchat.com/join/c4e7foogy6paz2sghjnbujov/

package litex_global

var PipelineInitCode = `
prop last_two_objects_are_equal(x, y, y2 obj):
	y = y2

know prop larger_is_transitive(x, y, z R):
	x > y
	y > z
	then:
		x > z

exist_prop a in_set st exist_obj_not_in_left_set_but_in_right_set(not_in_set, in_set set):
	not a $in not_in_set

"""
know forall small_set, big_set set:
	dom:
		len(small_set) < len(big_set)
	then:
		$exist_obj_not_in_left_set_but_in_right_set(small_set, big_set)
"""
`
