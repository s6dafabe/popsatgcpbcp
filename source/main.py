import argparse
import ModelRunners
import Utility
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--instance', type=str, required=True)
    parser.add_argument('--model', type=str, required=True)
    parser.add_argument('--timelimit', type=int, required=False)
    args = parser.parse_args()
    #clean_arguments = {k:v for k,v in vars(args).items() if v is not None}
    G = Utility.readDimacs(args.instance)
    # models = {
    #     "ASS":"ASS-I",
    #     "POP":"POP-I",
    #     "POPHyb":"POPH-I",
    #     "ASS_SAT":"ASS-S",
    #     "POP_SAT":"POP-S",
    #     "POPHyb_SAT":"POPH-S",
    #     "ASS_BCP":"ASS-I-B",
    #     "POP_BCP":"POP-I-B",
    #     "POPHyb_BCP":"POPH-I-B",
    #     "ASS_BCP_SAT":"ASS-S-B",
    #     "POP_BCP_SAT":"POP-S-B",
    #     "POPHyb_BCP_SAT":"POPH-S-B",
    # }
    if args.model[-1] == "B":
        result = ModelRunners.paperModelsBCP(args.model,G,args.timelimit if args.timelimit is not None else 3600)
    else:
        result = ModelRunners.paperModelsGCP(args.model, G, args.timelimit if args.timelimit is not None else 3600)
    for key,val in result.items():
        print(f"{key:<20}  {val}")


