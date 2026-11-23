/* Anvil v5 Cockpit Client Runtime — Visibility-Gated AbortController Sync,
 * Exponential Backoff, Zero UI-Click Poll Storms, Lazy Source Hydration,
 * and Manuscript-vs-Code Ground-Truth Divergence Panel Renderer.
 */
(function (root) {
  "use strict";

  var DEFAULT_BACKOFF_STEPS_MS = [1000, 2000, 4000, 8000];
  var DEFAULT_IDLE_POLL_MS = 12000;
  var MAX_IDLE_POLL_MS = 30000;

  function escHtml(val) {
    return String(val == null ? "" : val)
      .split("&").join("&amp;")
      .split("<").join("&lt;")
      .split(">").join("&gt;")
      .split('"').join("&quot;")
      .split("'").join("&#39;");
  }

  function stripDollars(txt) {
    return String(txt == null ? "" : txt).split("$").join("");
  }

  function normalizeSourcePayload(data) {
    if (!data || typeof data !== "object") {
      return { text: "", lines: [] };
    }
    var rawText = "";
    if (typeof data.content === "string") {
      rawText = data.content;
    } else if (typeof data.raw_source === "string") {
      rawText = data.raw_source;
    } else if (typeof data.source === "string") {
      rawText = data.source;
    }
    var lines = [];
    if (Array.isArray(data.lines) && data.lines.length > 0) {
      lines = data.lines.map(function (item, idx) {
        if (Array.isArray(item) && item.length >= 2) {
          return [Number(item[0]) || (idx + 1), String(item[1] == null ? "" : item[1])];
        }
        if (item && typeof item === "object") {
          return [Number(item.line) || (idx + 1), String(item.text == null ? "" : item.text)];
        }
        return [idx + 1, String(item == null ? "" : item)];
      });
    } else if (rawText) {
      lines = rawText.split("\r\n").join("\n").split("\n").map(function (ln, idx) {
        return [idx + 1, ln];
      });
    }
    return { text: rawText, lines: lines };
  }

  function normalizeVendorFamily(raw) {
    var f = String(raw == null ? "" : raw).trim().toLowerCase();
    if (f === "anthropic") return "claude";
    if (f === "google") return "gemini";
    if (f === "claude" || f === "gemini" || f === "chatgpt" || f === "grok") return f;
    return "";
  }

  function extractDivergences(bundle, rawSession) {
    var b = bundle || {};
    if (Array.isArray(b.divergences)) {
      return b.divergences;
    }
    var pm = (b.paper_map && typeof b.paper_map === "object")
      ? b.paper_map
      : ((rawSession && rawSession.paper_map && typeof rawSession.paper_map === "object") ? rawSession.paper_map : {});
    if (Array.isArray(pm.divergences)) {
      return pm.divergences;
    }
    return [];
  }

  function renderDivergencePanelHtml(bundle, rawSession, unknownState) {
    var b = bundle || {};
    var pm = (b.paper_map && typeof b.paper_map === "object")
      ? b.paper_map
      : ((rawSession && rawSession.paper_map && typeof rawSession.paper_map === "object") ? rawSession.paper_map : {});
    var rep = (pm && typeof pm.divergence_report === "object" && pm.divergence_report)
      || (b && typeof b.divergence_report === "object" && b.divergence_report)
      || null;
    var reportFailed = Boolean(rep && rep.ok === false);
    if (unknownState || reportFailed) {
      var errMsg = (rep && rep.error)
        ? String(rep.error)
        : "Divergence audit status UNKNOWN — backing store unreadable or detector did not complete cleanly.";
      return (
        '<section data-divergence-panel="true" data-divergence-status="UNKNOWN" class="card-block divergence-panel fault-card" aria-label="Manuscript vs Code Divergence Audit">' +
          '<div class="deck-row">' +
            '<strong>⚖ Manuscript ⇄ Code Ground-Truth Divergence Audit</strong>' +
            '<span class="div-cat-pill">UNKNOWN</span>' +
          '</div>' +
          '<div style="margin-top:6px; font-size:12px; color:#7A1E0A; font-weight:700;">' + escHtml(stripDollars(errMsg)) + '</div>' +
        '</section>'
      );
    }
    var divs = extractDivergences(b, rawSession);
    var hasPaper = Boolean(b.has_paper || pm.has_paper || divs.length > 0);
    if (!hasPaper) return "";
    var hasEvaluatedArray = Array.isArray(b.divergences) || Array.isArray(pm.divergences);
    if (!hasEvaluatedArray) {
      return (
        '<section data-divergence-panel="true" data-divergence-status="UNKNOWN" class="card-block divergence-panel fault-card" aria-label="Manuscript vs Code Divergence Audit">' +
          '<div class="deck-row">' +
            '<strong>⚖ Manuscript ⇄ Code Ground-Truth Divergence Audit</strong>' +
            '<span class="div-cat-pill">UNKNOWN</span>' +
          '</div>' +
          '<div style="margin-top:6px; font-size:12px; color:#7A1E0A; font-weight:700;">Divergence audit status UNKNOWN — divergence array has not been evaluated for this manuscript bundle.</div>' +
        '</section>'
      );
    }
    var nonDivCount = Number((rep && rep.documented_non_divergence_count) || 0);
    var statusAttr = divs.length === 0 ? "CLEAN" : "DIVERGENCES_FOUND";

    return (
      '<section data-divergence-panel="true" data-divergence-status="' + statusAttr + '" class="card-block divergence-panel" aria-label="Manuscript vs Code Divergence Audit">' +
        '<div class="deck-row">' +
          '<strong>⚖ Manuscript ⇄ Code Ground-Truth Divergence Audit</strong>' +
          '<div class="selector-group">' +
            '<span class="div-cat-pill">' + divs.length + ' divergence(s)</span>' +
            (nonDivCount > 0 ? '<span class="prov-tag traced">' + nonDivCount + ' documented aligned</span>' : '') +
          '</div>' +
        '</div>' +
        (divs.length === 0
          ? '<div style="margin-top:6px; font-size:12px; color:var(--ink-soft);">0 undocumented or contradicted estimation mechanisms detected between primary pipeline AST and manuscript.</div>'
          : divs.map(function (d) {
              var isContra = d.manuscript_status === "contradicted_in_manuscript";
              var msPillCls = "div-ms-pill" + (isContra ? " contradicted" : "");
              var msStatusLbl = isContra ? "CONTRADICTED IN MANUSCRIPT" : "ABSENT FROM MANUSCRIPT";
              var codeCite = d.code_citation || ((d.code_file || "") + ":L" + (d.code_line || 1));
              var sr = d.search_record || {};
              var srFiles = Array.isArray(sr.searched_files) ? sr.searched_files.join(", ") : (d.manuscript_entry || "manuscript");
              var srQueries = Array.isArray(sr.queries) ? sr.queries.slice(0, 3).join("; ") : "";
              var msCitationTxt = d.manuscript_root_citation || d.manuscript_citation || "";
              return (
                '<article class="div-item-card" data-divergence-id="' + escHtml(d.id || "") + '" data-divergence-category="' + escHtml(d.category || "") + '">' +
                  '<div class="deck-row">' +
                    '<div class="selector-group">' +
                      '<span class="div-cat-pill">' + escHtml(d.id || "DIV") + ' · ' + escHtml(d.category || "") + '</span>' +
                      '<span class="' + msPillCls + '">' + escHtml(msStatusLbl) + '</span>' +
                    '</div>' +
                    (d.code_file
                      ? '<button type="button" class="small-btn" data-jump-file="' + escHtml(d.code_file) + '" data-jump-line="' + Number(d.code_line || 1) + '"><code>' + escHtml(codeCite) + '</code> ⤢</button>'
                      : '') +
                  '</div>' +
                  '<div style="margin-top:5px; font-weight:800; font-size:12px;">' + escHtml(stripDollars(d.title || d.category_label || "")) + '</div>' +
                  '<div style="margin-top:3px; color:var(--ink-soft); font-size:11.5px;">' + escHtml(stripDollars(d.summary || "")) + '</div>' +
                  (d.code_snippet ? '<div class="div-code-snip">' + escHtml(d.code_snippet) + '</div>' : '') +
                  (isContra
                    ? '<div class="div-ms-box"><strong>Manuscript (' + escHtml(msCitationTxt) + '):</strong> "' + escHtml(stripDollars(d.manuscript_passage || "")) + '"</div>'
                    : '<div class="div-ms-box"><strong>Search Record (<code>absent_from_manuscript</code>):</strong> Searched <code>' + escHtml(srFiles) + '</code> for [' + escHtml(stripDollars(srQueries)) + '] · Closest section: <code>' + escHtml(stripDollars(sr.closest_section || "")) + '</code></div>') +
                '</article>'
              );
            }).join("")) +
      '</section>'
    );
  }

  function createSyncScheduler(opts) {
    var options = opts || {};
    var stats = options.stats || {
      inFlight: false,
      pollCount: 0,
      abortedCount: 0,
      failureStreak: 0,
      idleStreak: 0,
      lastBackoffMs: 0,
      pausedForVisibility: false
    };
    var backoffSteps = options.backoffStepsMs || DEFAULT_BACKOFF_STEPS_MS;
    var baseIdleMs = options.healthyPollMs || DEFAULT_IDLE_POLL_MS;
    var activeController = null;
    var timerId = null;
    var lastCallback = null;

    function clearTimer() {
      if (timerId !== null) {
        root.clearTimeout(timerId);
        timerId = null;
      }
    }

    function abortInFlight() {
      if (activeController) {
        try { activeController.abort(); } catch (_e) {}
        activeController = null;
        stats.inFlight = false;
        stats.abortedCount = (stats.abortedCount || 0) + 1;
      }
    }

    function nextErrorBackoffMs() {
      var idx = Math.min(stats.failureStreak || 0, backoffSteps.length - 1);
      var ms = backoffSteps[idx];
      stats.failureStreak = (stats.failureStreak || 0) + 1;
      stats.idleStreak = 0;
      stats.lastBackoffMs = ms;
      return ms;
    }

    function nextIdleDelayMs(hadChange) {
      stats.failureStreak = 0;
      stats.lastBackoffMs = 0;
      if (hadChange) {
        stats.idleStreak = 0;
        return baseIdleMs;
      }
      stats.idleStreak = Math.min(4, (stats.idleStreak || 0) + 1);
      return Math.min(MAX_IDLE_POLL_MS, baseIdleMs * Math.pow(1.5, stats.idleStreak - 1));
    }

    function schedule(delayMs, callback) {
      if (typeof callback === "function") {
        lastCallback = callback;
      }
      clearTimer();
      if (root.document && root.document.visibilityState !== "visible") {
        stats.pausedForVisibility = true;
        return;
      }
      stats.pausedForVisibility = false;
      timerId = root.setTimeout(function () {
        timerId = null;
        if (root.document && root.document.visibilityState !== "visible") {
          stats.pausedForVisibility = true;
          return;
        }
        if (typeof callback === "function") {
          callback();
        }
      }, delayMs);
    }

    function onVisibilityChange() {
      if (!root.document) return;
      if (root.document.visibilityState !== "visible") {
        clearTimer();
        abortInFlight();
        stats.pausedForVisibility = true;
      } else if (stats.pausedForVisibility && typeof lastCallback === "function") {
        stats.pausedForVisibility = false;
        schedule(0, lastCallback);
      }
    }

    if (root.document && typeof root.document.addEventListener === "function") {
      root.document.addEventListener("visibilitychange", onVisibilityChange);
    }

    function dispose() {
      clearTimer();
      abortInFlight();
      if (root.document && typeof root.document.removeEventListener === "function") {
        root.document.removeEventListener("visibilitychange", onVisibilityChange);
      }
    }

    function beginRequest(forceNow) {
      if (!forceNow && root.document && root.document.visibilityState !== "visible") {
        stats.pausedForVisibility = true;
        return null;
      }
      abortInFlight();
      var ctrl = new AbortController();
      activeController = ctrl;
      stats.inFlight = true;
      stats.pollCount = (stats.pollCount || 0) + 1;
      return ctrl;
    }

    function finishRequest(ctrl) {
      if (activeController === ctrl) {
        activeController = null;
        stats.inFlight = false;
      }
    }

    return {
      stats: stats,
      clearTimer: clearTimer,
      abortInFlight: abortInFlight,
      beginRequest: beginRequest,
      finishRequest: finishRequest,
      nextErrorBackoffMs: nextErrorBackoffMs,
      nextIdleDelayMs: nextIdleDelayMs,
      schedule: schedule,
      dispose: dispose
    };
  }

  function buildCopilotChatPayload(question, stateObj) {
    var st = stateObj || {};
    var rawFam = st.preferredFamily || (st.bundle && st.bundle.xval_receipt && st.bundle.xval_receipt.orchestrator_family) || "";
    var preferredFamily = normalizeVendorFamily(rawFam);
    var parsedLine = parseInt(st.activeLine, 10);
    var payload = {
      question: String(question == null ? "" : question).trim(),
      active_stage_id: st.activeStageId || "S1",
      active_file: st.activeFile || "",
      active_line: (Number.isFinite(parsedLine) && parsedLine >= 1) ? parsedLine : 1,
      ide_open: Boolean(st.ideOpen),
      live: true
    };
    if (preferredFamily) {
      payload.preferred_family = preferredFamily;
    }
    return payload;
  }

  root.AnvilV5Client = {
    escHtml: escHtml,
    stripDollars: stripDollars,
    normalizeVendorFamily: normalizeVendorFamily,
    normalizeSourcePayload: normalizeSourcePayload,
    extractDivergences: extractDivergences,
    renderDivergencePanelHtml: renderDivergencePanelHtml,
    createSyncScheduler: createSyncScheduler,
    buildCopilotChatPayload: buildCopilotChatPayload
  };
})(window);
