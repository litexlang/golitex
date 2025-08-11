import json
import os

json_data = []

for file in os.listdir("examples/compare_with_lean"):
    if file.endswith(".lix"):
        with open(f"examples/compare_with_lean/{file}", "r") as f:
            lix_code = f.read()

        # 如果 f 的开头是 # 开头，那把这个comment做成informal_statement
        informal_statement = ""
        if lix_code.startswith("#"):
            informal_statement = lix_code.split("\n")[0]
            # informal_statement 去掉 #
            informal_statement = informal_statement.replace("#", "")
            # 把 informal statement 开头的空格去掉
            informal_statement = informal_statement.strip()

            lix_code = "\n".join(lix_code.split("\n")[1:])
        elif lix_code.startswith("\"\"\""):
            # 遍历，直到某一行的开头也是"""
            for i in range(len(lix_code.split("\n"))):
                if lix_code.split("\n")[i].startswith("\"\"\""):
                    informal_statement = "\n".join(lix_code.split("\n")[i+1:])
                    # informal_statement 去掉 """
                    informal_statement = informal_statement.replace("\"\"\"", "")
                    # 把 informal statement 开头的空格去掉
                    informal_statement = informal_statement.strip()
                    lix_code = "\n".join(lix_code.split("\n")[:i])
                    break
        else:
            informal_statement = ""

        # 把 # 开头的 全部去掉
        lix_code = "\n".join([line for line in lix_code.split("\n") if not line.startswith("#")])

        # 如果 某一行是 """ 开头，那找到这一行，然后找到这一行后面的第一个 """ ，把这一行和这一行后面的所有行都去掉
        for i in range(len(lix_code.split("\n"))):
            if lix_code.split("\n")[i].startswith("\"\"\""):
                lix_code = "\n".join(lix_code.split("\n")[:i])
                break

        json_data.append({
            "id": file,
            "informal_statement": informal_statement,
            "litex_code": lix_code
        })

with open("./past_examples/lix_to_json.json", "w") as f:
    json.dump(json_data, f, indent=4)