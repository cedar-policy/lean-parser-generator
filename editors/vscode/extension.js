// Copyright Cedar Contributors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Minimal VS Code client for the .lig language server.
//
// It launches the `lig-language-server` executable over stdio and lets
// vscode-languageclient drive the LSP handshake (initialize / didOpen /
// didChange / publishDiagnostics / shutdown). The server itself only needs to
// publish diagnostics; everything else is handled here.

const fs = require("fs");
const path = require("path");
const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

/** Resolve the server executable path from settings or the workspace default. */
function resolveServerPath() {
  const configured = vscode.workspace.getConfiguration("lig").get("serverPath");
  if (configured && configured.trim() !== "") {
    return configured;
  }
  const folders = vscode.workspace.workspaceFolders;
  if (folders && folders.length > 0) {
    return path.join(
      folders[0].uri.fsPath,
      ".lake",
      "build",
      "bin",
      "lig-language-server"
    );
  }
  return null;
}

function activate(context) {
  const serverPath = resolveServerPath();
  if (!serverPath || !fs.existsSync(serverPath)) {
    vscode.window.showErrorMessage(
      `lig-language-server not found${serverPath ? ` at ${serverPath}` : ""}. ` +
        "Build it with `lake build lig-language-server`, or set `lig.serverPath`."
    );
    return;
  }

  // The server communicates over stdio with Content-Length framing.
  const serverOptions = {
    run: { command: serverPath, transport: TransportKind.stdio },
    debug: { command: serverPath, transport: TransportKind.stdio },
  };

  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "lig" }],
    // Full document sync matches the server's TextDocumentSyncKind.Full.
  };

  client = new LanguageClient(
    "lig",
    "LIG Language Server",
    serverOptions,
    clientOptions
  );

  context.subscriptions.push(client);
  client.start();
}

function deactivate() {
  if (!client) {
    return undefined;
  }
  return client.stop();
}

module.exports = { activate, deactivate };
