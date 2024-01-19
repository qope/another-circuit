import { ethers } from "hardhat";
import { readFile } from "./readFile";

async function main() {
  const signer = (await ethers.getSigners())[0]

  const yulBytecode = await readFile("../deployment_code.txt")
  const factory = ethers.ContractFactory.fromSolidity(
    { bytecode: yulBytecode, abi: [] },
    signer
  )
  const yulVerifier = await factory.deploy()
  await yulVerifier.deployed()

  console.log("Contract deployed to:", yulVerifier.address)
}

// We recommend this pattern to be able to use async/await everywhere
// and properly handle errors.
main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
