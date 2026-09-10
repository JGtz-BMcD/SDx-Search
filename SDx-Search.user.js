// ==UserScript==
// @name         SDx Search
// @namespace    https://github.com/JGtz-BMcD/SDx-Search
// @version      1.0
// @description  SDx Search: live as-you-type preview (searches SDx and your local content index), a results overlay on the new SDx tab, advanced filters, side-bar launcher, and an opportunistic local content index
// @match        https://*.intergraphsmartcloud.com/*
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_xmlhttpRequest
// @connect      self
// @require      https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.min.js
// @require      https://cdnjs.cloudflare.com/ajax/libs/jszip/3.10.1/jszip.min.js
// @run-at       document-start
// @noframes
// @downloadURL https://raw.githubusercontent.com/JGtz-BMcD/SDx_Search/main/SDx-Search.user.js
// @updateURL https://raw.githubusercontent.com/JGtz-BMcD/SDx_Search/main/SDx-Search.user.js
// @Author        Josue Gutierrez
// ==/UserScript==
(function () {
    'use strict';
    const RIGHT_OFFSET = 122;
    const DEFAULT_ENTITY_TYPE = 'AllDocuments_68290'; // NOTE (audit): only used when no existing filter to inherit
                                                        // entityType from. If a project's "All Documents" view uses a
                                                        // different entity id, a brand-new base for that project could
                                                        // query the wrong entity. Left as-is pending confirmation.
    const PENDING_SEARCH_MAX_AGE_MS = 10 * 60 * 1000;
    const DISCIPLINE_CODES = [
        'AA', 'AR', 'BA', 'CE', 'CH', 'CS', 'CX',
        'EA', 'EC', 'EL', 'EN', 'GE', 'IC', 'IM',
        'IN', 'ME', 'MX', 'PL', 'PR', 'QA', 'SA',
        'ST', 'TE'
    ];
    // Content index constants
    const INDEX_DB_NAME = 'sdxContentIndexDB';
    const INDEX_DB_VERSION = 1;
    const INDEX_STORE_NAME = 'documents';
    const DEFAULT_INDEX_DOC_LIMIT = 250;
    const PDF_WORKER_SRC = 'https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js';
    const DEFAULT_PANEL_WIDTH_PX = 420; // was 370, bumped +50px per request
    const MIN_PANEL_WIDTH_PX = 300;
    const MAX_PANEL_WIDTH_PX = 900;
    const DEFAULT_AUTO_CLOSE_SECONDS = 60;
    const LIVE_SEARCH_DEBOUNCE_MS = 400;
    const LIVE_SEARCH_MIN_CHARS = 2;
    function getPanelWidthPx() {
        const value = Number(GM_getValue('sdxPanelWidthPx', DEFAULT_PANEL_WIDTH_PX)) || DEFAULT_PANEL_WIDTH_PX;
        return Math.min(MAX_PANEL_WIDTH_PX, Math.max(MIN_PANEL_WIDTH_PX, value));
    }

    const savedHeuristic = GM_getValue('sdxHeuristic', 'broadAllWords');
    const savedContractField = GM_getValue('sdxContractField', '');
    const savedContractValue = GM_getValue('sdxContractValue', '');
    const savedGenericFilterType = GM_getValue('sdxGenericFilterType', '');
    const savedIssueDate = GM_getValue('sdxIssueDate', '');
    const savedDisciplines = GM_getValue('sdxDisciplines', []);
    const savedStatus = GM_getValue('sdxStatus', '');
    const savedWpContract = GM_getValue('sdxWpContract', '');
    const savedWpNeedSendOut = GM_getValue('sdxWpNeedSendOut', false);

    let currentTabId = 'search';
    let cachedIndexDocuments = null;

    // Installed immediately, synchronously, at document-start - before
    // Angular has even begun bootstrapping, let alone fired its first
    // automatic API call (the dashboard's own auto-loading widgets: docs to
    // resubmit, notifications, milestones, etc. all fire authenticated
    // requests during boot with zero action from the user). Patching
    // fetch/XMLHttpRequest doesn't need the DOM to exist, so there's no
    // reason to wait - waiting is exactly what caused those very first
    // requests (and their Authorization header) to go unseen, making it
    // look like a manual search was required to "prime" a token that was
    // actually available the whole time.
    initContentIndexCapture();

    setTimeout(() => {
        if (isRawFileViewerPage()) {
            // A document opened directly in its own tab (SDx's native file
            // viewer, e.g. Edge's built-in PDF renderer). There's no SDx app
            // UI here to search or warm up, and no side-bar to inject into -
            // just capture the file for the content index and stop, so the
            // panel/launcher never show up on these tabs.
            captureCurrentRawFilePage();
            return;
        }
        rememberCurrentSearchPageIfApplicable();
        checkForPendingWarmup();
        checkForPendingCriteria();
        checkForPendingResultsOverlay();
        createPanel();
        installLauncher();
        installOutsideClickHandler();
    }, 1500);
    // ============================================================
    // Search base storage
    // ============================================================
    function getSearchBases() {
        const bases = GM_getValue('sdxSearchBasesByProject', {});
        return bases && typeof bases === 'object' ? bases : {};
    }
    function saveSearchBases(bases) {
        GM_setValue('sdxSearchBasesByProject', bases || {});
    }
    // A real SDx project/config key looks like "PR_186688" - short, plain
    // alphanumerics. Some routes (e.g. /dashboards) reuse "selected=" in the
    // hash for something else entirely (selected asset codes for a widget,
    // not a project), which the naive regex below would otherwise mistake
    // for a project key. Filtering to this shape stops that from corrupting
    // sdxLastActiveProjectKey / the saved search bases.
    function isLikelyValidProjectKey(key) {
        return typeof key === 'string' && key.length > 0 && key.length <= 40 && /^[A-Za-z0-9_.-]+$/.test(key);
    }
    function getCurrentProjectKey() {
        const hash = window.location.hash || '';
        const selectedMatch = hash.match(/selected=([^;]+)/);
        if (selectedMatch && selectedMatch[1]) {
            const candidate = decodeURIComponent(selectedMatch[1]);
            if (isLikelyValidProjectKey(candidate)) return candidate;
        }
        const configMatch = hash.match(/config=([^;]+)/);
        if (configMatch && configMatch[1]) {
            try {
                const parsed = JSON.parse(decodeURIComponent(configMatch[1]));
                if (Array.isArray(parsed)) {
                    // Some pages (e.g. a consolidated "To Do List" spanning
                    // multiple projects) legitimately carry more than one
                    // project key in config=[...]. There's no reliable way to
                    // tell which one the user is actually looking at from the
                    // hash alone in that case - blindly trusting parsed[0]
                    // used to confidently return whichever key happened to
                    // sort first, which is actively wrong (not "the current
                    // project" at all), and was overriding a correctly-set
                    // default project with an arbitrary one. Only trust this
                    // when there's exactly one valid key - otherwise this is
                    // genuinely ambiguous, so report unknown instead of
                    // guessing.
                    const validKeys = parsed.filter(isLikelyValidProjectKey);
                    if (validKeys.length === 1) return validKeys[0];
                    return '';
                }
            } catch (error) {
                console.warn('SDx Searcher: Could not parse config from URL.', error);
            }
        }
        return '';
    }
    function getBestProjectKeyForSearch() {
        // Priority, most to least trustworthy:
        // 1. Whatever the user has manually selected in our own dropdown
        //    right now - the most direct, immediate expression of intent,
        //    always honored even if it differs from the pinned default below.
        // 2. The pinned "Project to search" default from Settings, if one is
        //    set - this is now the single, authoritative override (replacing
        //    the old separate "force" checkbox, which was easy to forget to
        //    also turn on, leaving the default silently ignored). Once set,
        //    it wins unconditionally over whatever SDx's own page looks like
        //    it's showing, since auto-detection can't always be trusted (see
        //    getCurrentProjectKey()'s notes on ambiguous multi-project pages).
        // 3. Auto-detected from the current page, only when unambiguous.
        // 4. Whatever project was last active.
        // 5. If there's only one saved project at all, that one.
        const bases = getSearchBases();
        const selector = document.getElementById('sdx-project-base');
        if (selector && selector.value && bases[selector.value]) return selector.value;
        const preferredKey = GM_getValue('sdxPreferredProjectKey', '');
        if (preferredKey && bases[preferredKey]) return preferredKey;
        const currentKey = getCurrentProjectKey();
        if (currentKey && bases[currentKey]) return currentKey;
        const lastActive = GM_getValue('sdxLastActiveProjectKey', '');
        if (lastActive && bases[lastActive]) return lastActive;
        const keys = Object.keys(bases).filter(isLikelyValidProjectKey);
        if (keys.length === 1) return keys[0];
        return '';
    }
    function rememberCurrentSearchPageIfApplicable() {
        const hash = window.location.hash || '';
        const projectKey = getCurrentProjectKey();
        if (!projectKey) return;
        GM_setValue('sdxLastActiveProjectKey', projectKey);
        if (hash.includes('queryFilter=')) {
            const bases = getSearchBases();
            bases[projectKey] = window.location.href;
            saveSearchBases(bases);
        }
    }
    function setCurrentPageAsSearchBase() {
        if (!currentPageHasQueryFilter()) {
            alert('Open a working SDx document list or search results page first, then click Set Current Page as Search Base.');
            return;
        }
        const projectKey = getCurrentProjectKey();
        if (!projectKey) {
            alert('Could not detect the current SDx project/config from this page.');
            return;
        }
        const bases = getSearchBases();
        bases[projectKey] = window.location.href;
        saveSearchBases(bases);
        GM_setValue('sdxLastActiveProjectKey', projectKey);
        refreshProjectBaseDropdown();
        const status = document.getElementById('sdx-page-status');
        if (status) status.innerHTML = getPageModeMessage();
        alert('Search base saved for project/config: ' + projectKey);
    }
    // ============================================================
    // Pending criteria warm-up
    // Important change:
    // We save search criteria, not the final queryFilter.
    // The final queryFilter is rebuilt after SDx opens the saved list page.
    // ============================================================
    function savePendingCriteria(criteria, projectKey) {
        GM_setValue('sdxPendingCriteria', {
            created: Date.now(),
            projectKey: projectKey || '',
            criteria: criteria
        });
    }
    function clearPendingCriteria() {
        GM_setValue('sdxPendingCriteria', null);
    }
    function checkForPendingCriteria() {
        if (!currentPageHasQueryFilter()) return;
        const pending = GM_getValue('sdxPendingCriteria', null);
        if (!pending || !pending.criteria) return;
        const age = Date.now() - (pending.created || 0);
        if (age > PENDING_SEARCH_MAX_AGE_MS) {
            clearPendingCriteria();
            return;
        }
        const currentKey = getCurrentProjectKey();
        if (pending.projectKey && currentKey && pending.projectKey !== currentKey) {
            return;
        }
        clearPendingCriteria();
        setTimeout(() => {
            applyCriteriaOnCurrentList(pending.criteria);
        }, 900);
    }
    // ============================================================
    // Warm-up bootstrap fix
    //
    // Root cause (confirmed): opening a saved deep-link URL (one that already
    // contains queryFilter=... in the hash) directly in a brand-new tab via
    // window.open() makes SDx's auth guard fail ("authentication failed"),
    // even though the session is perfectly valid in the tab you already had
    // open. This matches a SPA that only completes its login/bootstrap
    // sequence cleanly when it starts from a "plain" URL, not a cold deep link.
    //
    // Fix: open the new tab at the saved base URL with its hash stripped off
    // (a plain, bootstrap-friendly URL) and let SDx authenticate normally.
    // Once that's done, this script (running fresh in that new tab) performs
    // a same-tab navigation to the *real* saved deep link. Because that's now
    // a normal in-app navigation on an already-authenticated tab rather than
    // a brand-new browsing context's first request, it should avoid the
    // auth-guard failure. The existing pending-criteria mechanism then takes
    // over exactly as before once that deep link has loaded.
    // ============================================================
    function stripHashFromUrl(url) {
        try {
            const parsed = new URL(url);
            parsed.hash = '';
            return parsed.toString();
        } catch (error) {
            const hashIndex = url.indexOf('#');
            return hashIndex === -1 ? url : url.slice(0, hashIndex);
        }
    }
    function savePendingWarmup(projectKey, targetUrl) {
        GM_setValue('sdxPendingWarmup', {
            created: Date.now(),
            projectKey: projectKey || '',
            targetUrl: targetUrl
        });
    }
    function clearPendingWarmup() {
        GM_setValue('sdxPendingWarmup', null);
    }
    function checkForPendingWarmup() {
        const pending = GM_getValue('sdxPendingWarmup', null);
        if (!pending || !pending.targetUrl) return;
        const age = Date.now() - (pending.created || 0);
        if (age > PENDING_SEARCH_MAX_AGE_MS) {
            clearPendingWarmup();
            return;
        }
        if (currentPageHasQueryFilter()) {
            // Already on a working list page somehow; nothing to bootstrap.
            clearPendingWarmup();
            return;
        }
        clearPendingWarmup();
        // Give SDx a moment to finish logging in / bootstrapping on this clean
        // URL before navigating (same tab, same session) to the real deep link.
        setTimeout(() => {
            // pending.targetUrl is now the FINAL, already-filtered results URL
            // (built up front by buildFinalTargetUrl()) - not an intermediate
            // stop that still needs its criteria swapped in later, the way it
            // used to be. So this one navigation is the only one needed.
            window.location.href = pending.targetUrl;
            // Root-cause fix: the bootstrap URL and the target URL share the
            // same origin+path and differ only by hash, so the line above is
            // a same-document navigation - the browser does NOT reload for
            // that, which means this script never runs again on its own to
            // pick up on the new page. A raw hash change also isn't
            // guaranteed to fully re-bootstrap an Angular lazy-loaded module
            // the way a real navigation does, which likely explains the
            // "exception occurred" / missing-column errors seen early in this
            // project on top of the stale-criteria problem that fix also
            // solved. Forcing an actual reload here fixes both: it lands this
            // tab on a fully-booted results page showing the real filters,
            // where the real filters are visible (checkForPendingResultsOverlay()
            // doesn't actually need to wait for this reload, though - it
            // already ran and showed its popup back on the bootstrap page).
            setTimeout(() => {
                window.location.reload();
            }, 300);
        }, 2500);
    }
    // ============================================================
    // Launcher (floating button - fallback only, see side-bar launcher below)
    // ============================================================
    function createLauncherButton() {
        if (document.getElementById('sdx-wizard-launcher')) return;
        const launcher = document.createElement('button');
        launcher.id = 'sdx-wizard-launcher';
        launcher.title = 'Open SDx Searcher';
        launcher.innerHTML = `
            <div style="display:flex; align-items:center; gap:6px;">
                <span style="font-size:22px; line-height:1;">🕵️</span>
                <span style="font-weight:700;">SDx Searcher</span>
            </div>
        `;
        launcher.style.cssText = `
            position: fixed;
            bottom: 22px;
            right: ${RIGHT_OFFSET}px;
            z-index: 999999;
            padding: 8px 12px;
            background: linear-gradient(135deg, #3b1d72, #0078d4);
            color: #ffffff;
            border: 1px solid rgba(255,255,255,0.45);
            border-radius: 999px;
            cursor: pointer;
            box-shadow: 0 4px 12px rgba(0,0,0,0.35);
            font-family: Arial, sans-serif;
            font-size: 13px;
            transition: transform 0.12s ease, box-shadow 0.12s ease;
        `;
        launcher.addEventListener('mouseenter', () => {
            launcher.style.transform = 'scale(1.04)';
            launcher.style.boxShadow = '0 6px 16px rgba(0,0,0,0.45)';
        });
        launcher.addEventListener('mouseleave', () => {
            launcher.style.transform = 'scale(1.00)';
            launcher.style.boxShadow = '0 4px 12px rgba(0,0,0,0.35)';
        });
        launcher.addEventListener('click', () => {
            rememberCurrentSearchPageIfApplicable();
            clearSearchTextOnOpen();
            togglePanel();
        });
        document.body.appendChild(launcher);
    }
    function removeFloatingLauncherIfPresent() {
        const existing = document.getElementById('sdx-wizard-launcher');
        if (existing) existing.remove();
    }
    // ============================================================
    // Launcher (SDx side-bar integration)
    //
    // Preferred launcher location: inside SDx's own left-hand nav
    // (nav.side-bar), as a new icon button, so it stops floating on top of
    // list content. The side-bar is rendered by Angular after the app
    // bootstraps, so we watch for it with a MutationObserver instead of
    // assuming it exists at script-init time. If it never shows up (e.g. a
    // page that doesn't have that nav), we fall back to the floating button
    // so the tool still works everywhere.
    // ============================================================
    function createSideBarButton() {
        const button = document.createElement('button');
        button.id = 'side_bar_sdx_searcher_btn';
        button.className = 'side-bar__button';
        button.title = 'SDx Searcher';
        // Default Windows "Detective" emoji, left in its native color on
        // purpose - it stands out against the sidebar's monochrome icons
        // rather than blending in with them.
        const icon = document.createElement('span');
        icon.textContent = '\u{1F575}\u{FE0F}';
        icon.style.fontSize = '20px';
        icon.style.lineHeight = '1';
        button.appendChild(icon);
        button.addEventListener('click', () => {
            rememberCurrentSearchPageIfApplicable();
            clearSearchTextOnOpen();
            togglePanel();
        });
        return button;
    }
    // SDx's own button styling is Angular view-encapsulated: the real CSS
    // rules for .side-bar__button only match elements carrying that
    // component's auto-generated _ngcontent-* attribute, which our injected
    // button can never have. Left alone, that means our button falls back to
    // plain browser button chrome (white background, default border, no
    // sizing) - which is exactly the "ghetto, off-center, white background"
    // look. Fix: copy the *actual computed* styles off a real sibling button
    // at runtime instead of relying on any stylesheet to reach our element.
    function copyButtonVisualStyle(sourceButton, targetButton) {
        try {
            const computed = window.getComputedStyle(sourceButton);
            const propsToCopy = [
                'width', 'height', 'minWidth', 'minHeight', 'boxSizing',
                'display', 'alignItems', 'justifyContent',
                'padding', 'margin', 'border', 'borderRadius',
                'color', 'cursor', 'fontSize'
            ];
            propsToCopy.forEach(prop => {
                targetButton.style[prop] = computed[prop];
            });
            targetButton.style.background = 'transparent';
            targetButton.style.outline = 'none';
        } catch (error) {
            console.warn('SDx Searcher: Could not copy side-bar button style.', error);
        }
    }
    function findSideBarAnchor(nav) {
        // Prefer landing right next to the existing "Advanced Search" icon,
        // since that's the closest existing analog to this tool. Fall back
        // to any existing button's group, then any group at all.
        const queryBtn = nav.querySelector('#side_bar_query-btn');
        if (queryBtn && queryBtn.parentElement) {
            return { section: queryBtn.parentElement, sample: queryBtn };
        }
        const anyButton = nav.querySelector('.side-bar__button');
        if (anyButton && anyButton.parentElement) {
            return { section: anyButton.parentElement, sample: anyButton };
        }
        const anyGroup = nav.querySelector('section.side-bar__group');
        return anyGroup ? { section: anyGroup, sample: null } : null;
    }
    function installSideBarLauncher() {
        if (document.getElementById('side_bar_sdx_searcher_btn')) return true;
        const nav = document.querySelector('nav.side-bar');
        if (!nav) return false;
        const anchor = findSideBarAnchor(nav);
        if (!anchor) return false;
        const button = createSideBarButton();
        if (anchor.sample) {
            copyButtonVisualStyle(anchor.sample, button);
        }
        // Append into an EXISTING, already-styled group rather than a brand
        // new <section>, so the existing group's flex/gap/alignment rules
        // (which also only apply via Angular's scoped attribute, and which
        // we likewise cannot recreate for a new section) still govern our
        // button's layout instead of leaving it visually adrift.
        anchor.section.appendChild(button);
        return true;
    }
    function installLauncher() {
        if (installSideBarLauncher()) return;
        let settled = false;
        // Keep watching indefinitely - only stop once the side-bar actually
        // shows up. A slow bootstrap (cold cache, an SSO round-trip, a busy
        // day) can easily take longer than any fixed timeout, and a
        // userscript gets exactly one shot per real page load: giving up
        // and disconnecting used to lock in the floating fallback for the
        // rest of that tab's life even if the side-bar appeared moments
        // later. Now the floating button is only ever an *interim* stand-in
        // while we keep looking, and gets swapped out the moment the
        // side-bar is found.
        const observer = new MutationObserver(() => {
            if (installSideBarLauncher()) {
                settled = true;
                observer.disconnect();
                removeFloatingLauncherIfPresent();
            }
        });
        observer.observe(document.body, { childList: true, subtree: true });
        setTimeout(() => {
            if (!settled) {
                createLauncherButton();
            }
        }, 8000);
    }
    // ============================================================
    // Panel
    // ============================================================
    function createPanel() {
        if (document.getElementById('sdx-search-helper')) return;
        const panel = document.createElement('div');
        panel.id = 'sdx-search-helper';
        panel.innerHTML = `
            <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:8px;">
                <div style="font-weight:700; font-size:14px;">
                    🕵️ SDx Searcher
                </div>
                <button id="sdx-close-panel"
                        title="Close"
                        style="
                            border:none;
                            background:transparent;
                            font-size:16px;
                            cursor:pointer;
                            color:#555;
                        ">
                    ✕
                </button>
            </div>
            <div style="display:flex; gap:6px; margin-bottom:10px; flex-wrap:wrap;">
                <button id="sdx-tab-search"
                        style="
                            padding:6px 10px;
                            cursor:pointer;
                            background:#0078d4;
                            color:white;
                            border:none;
                            border-radius:4px;
                            font-weight:600;
                        ">
                    Searcher
                </button>
                <button id="sdx-tab-work-package"
                        style="
                            padding:6px 10px;
                            cursor:pointer;
                            background:#f3f3f3;
                            color:#222;
                            border:1px solid #bbb;
                            border-radius:4px;
                            font-weight:600;
                        ">
                    Work Package Helper
                </button>
                <button id="sdx-tab-index"
                        style="
                            padding:6px 10px;
                            cursor:pointer;
                            background:#f3f3f3;
                            color:#222;
                            border:1px solid #bbb;
                            border-radius:4px;
                            font-weight:600;
                        ">
                    Content Index
                </button>
                <button id="sdx-tab-settings"
                        style="
                            padding:6px 10px;
                            cursor:pointer;
                            background:#f3f3f3;
                            color:#222;
                            border:1px solid #bbb;
                            border-radius:4px;
                            font-weight:600;
                        ">
                    Settings
                </button>
            </div>
            <div id="sdx-page-status"
                 style="
                    font-size:11px;
                    color:#555;
                    background:#f8f8f8;
                    border:1px solid #ddd;
                    padding:6px;
                    border-radius:4px;
                    margin-bottom:8px;
                    line-height:1.35;
                 ">
                ${getPageModeMessage()}
            </div>
            <div id="sdx-project-base-block" style="
                font-size:11px;
                color:#555;
                background:#fffdf3;
                border:1px solid #e0d48a;
                padding:6px;
                border-radius:4px;
                margin-bottom:10px;
                line-height:1.35;
            ">
                <div style="font-weight:600; margin-bottom:4px;">Project search base:</div>
                <select id="sdx-project-base"
                        style="
                            width:324px;
                            padding:5px;
                            margin-bottom:6px;
                            border:1px solid #aaa;
                            border-radius:4px;
                        ">
                    ${buildProjectBaseOptionsHtml()}
                </select>
                <button id="sdx-save-current-base"
                        style="
                            padding:5px 9px;
                            cursor:pointer;
                            background:#605e5c;
                            color:white;
                            border:none;
                            border-radius:4px;
                        ">
                    Set Current Page as Search Base
                </button>
            </div>
            <div id="sdx-search-tab-content">
                <label for="sdx-search-text" style="display:block; margin-bottom:3px;">
                    Search text:
                </label>
                <input id="sdx-search-text"
                       type="text"
                       placeholder="Example: RICE SB 210, WEG, XFMR..."
                       value=""
                       style="
                           width:310px;
                           padding:6px;
                           margin-bottom:8px;
                           border:1px solid #aaa;
                           border-radius:4px;
                       ">
                <label for="sdx-heuristic" style="display:block; margin-bottom:3px;">
                    Search heuristic:
                </label>
                <select id="sdx-heuristic"
                        style="
                            width:324px;
                            padding:6px;
                            margin-bottom:8px;
                            border:1px solid #aaa;
                            border-radius:4px;
                        ">
                    <option value="broadAllWords">Broad search, match all words</option>
                    <option value="broadPhrase">Broad search, exact typed phrase</option>
                    <option value="documentAllWords">Document name, match all words</option>
                    <option value="documentPhrase">Document name, exact typed phrase</option>
                    <option value="filenameAllWords">Filename, match all words</option>
                    <option value="filenamePhrase">Filename, exact typed phrase</option>
                    <option value="titleAllWords">Title, match all words</option>
                    <option value="titlePhrase">Title, exact typed phrase</option>
                    <option value="contractAllWords">Contract, match all words</option>
                    <option value="exactDocument">Exact document name</option>
                    <option value="exactFilename">Exact filename</option>
                </select>
                <label for="sdx-contract-field" style="display:block; margin-bottom:3px;">
                    Contract filter:
                </label>
                <select id="sdx-contract-field"
                        style="
                            width:324px;
                            padding:6px;
                            margin-bottom:6px;
                            border:1px solid #aaa;
                            border-radius:4px;
                        ">
                    <option value="">No contract filter</option>
                    <option value="From_Contract">From Contract contains</option>
                    <option value="To_Contract">To Contract contains</option>
                </select>
                <input id="sdx-contract-value"
                       type="text"
                       placeholder="Example: 8220 or 186688-5.8220"
                       value="${escapeHtml(savedContractValue)}"
                       style="
                           width:310px;
                           padding:6px;
                           margin-bottom:10px;
                           border:1px solid #aaa;
                           border-radius:4px;
                       ">
                <label for="sdx-generic-filter-type" style="display:block; margin-bottom:3px;">
                    Generic filter:
                </label>
                <select id="sdx-generic-filter-type"
                        style="
                            width:324px;
                            padding:6px;
                            margin-bottom:8px;
                            border:1px solid #aaa;
                            border-radius:4px;
                        ">
                    <option value="">No generic filter</option>
                    <option value="issueDateNewer">Issue Date newer than</option>
                    <option value="issueDateOlder">Issue Date older than</option>
                    <option value="discipline">Discipline codes</option>
                    <option value="status">Status</option>
                </select>
                <div id="sdx-issue-date-box" style="display:none; margin-bottom:10px;">
                    <input id="sdx-issue-date"
                           type="date"
                           value="${escapeHtml(savedIssueDate)}"
                           style="
                               width:310px;
                               padding:6px;
                               border:1px solid #aaa;
                               border-radius:4px;
                           ">
                </div>
                <div id="sdx-discipline-box"
                     style="
                         display:none;
                         margin-bottom:10px;
                         max-height:125px;
                         overflow:auto;
                         border:1px solid #ddd;
                         border-radius:6px;
                         padding:8px;
                         background:#fafafa;
                     ">
                    ${buildDisciplineCheckboxHtml()}
                </div>
                <div id="sdx-status-box" style="display:none; margin-bottom:10px;">
                    <select id="sdx-status"
                            style="
                                width:324px;
                                padding:6px;
                                border:1px solid #aaa;
                                border-radius:4px;
                            ">
                        <option value="">Select status</option>
                        <option value="approved">Approved</option>
                        <option value="hold">Hold</option>
                    </select>
                </div>
                <div style="display:flex; gap:6px; margin-bottom:8px;">
                    <button id="sdx-apply-search"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#0078d4;
                                color:white;
                                border:none;
                                border-radius:4px;
                            ">
                        SDx Search
                    </button>
                    <button id="sdx-clear-search"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#f3f3f3;
                                color:#222;
                                border:1px solid #bbb;
                                border-radius:4px;
                            ">
                        Reset Form
                    </button>
                </div>
                <div style="font-size:11px; color:#666; line-height:1.35;">
                    Preview updates live as you type. Click SDx Search to open the full, interactive SDx results in a new tab, so you can use SDx's own tools (Actions, etc.) on what comes back.
                </div>
            </div>
            <div id="sdx-work-package-tab-content" style="display:none;">
                <label for="sdx-wp-contract" style="display:block; margin-bottom:3px;">
                    Contract number:
                </label>
                <input id="sdx-wp-contract"
                       type="text"
                       placeholder="Example: 8220 or 186688-5.8220"
                       value="${escapeHtml(savedWpContract)}"
                       style="
                           width:310px;
                           padding:6px;
                           margin-bottom:10px;
                           border:1px solid #aaa;
                           border-radius:4px;
                       ">
                <div style="
                    padding:8px;
                    background:#f8f8f8;
                    border:1px solid #ddd;
                    border-radius:6px;
                    margin-bottom:10px;
                ">
                    <label style="display:flex; align-items:flex-start; gap:7px; cursor:pointer;">
                        <input id="sdx-wp-need-send-out"
                               type="checkbox"
                               style="margin-top:2px;">
                        <span>
                            <b>Document needing to be sent out</b><br>
                            <span style="font-size:11px; color:#666;">
                                To Contract contains the contract number and Transmittal does not contain the contract number.
                            </span>
                        </span>
                    </label>
                </div>
                <div style="display:flex; gap:6px; margin-bottom:8px;">
                    <button id="sdx-wp-apply"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#107c10;
                                color:white;
                                border:none;
                                border-radius:4px;
                            ">
                        Run Helper
                    </button>
                    <button id="sdx-wp-clear"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#f3f3f3;
                                color:#222;
                                border:1px solid #bbb;
                                border-radius:4px;
                            ">
                        Reset Form
                    </button>
                </div>
            </div>
            <div id="sdx-search-results-wrapper" style="display:none;">
                <div style="font-weight:600; font-size:12px; margin-bottom:4px;">Results:</div>
                <div id="sdx-search-results"
                     style="
                         max-height:260px;
                         overflow-y:auto;
                         border:1px solid #ddd;
                         border-radius:6px;
                         padding:2px;
                         margin-bottom:4px;
                     "></div>
            </div>
            <div id="sdx-index-tab-content" style="display:none;">
                <div style="
                    font-size:11px;
                    color:#555;
                    background:#f5f0fb;
                    border:1px solid #d8c7ef;
                    padding:8px;
                    border-radius:6px;
                    margin-bottom:10px;
                    line-height:1.4;
                    word-wrap:break-word;
                    overflow-wrap:break-word;
                ">
                    Builds a local, text-only search cache of documents you open in SDx
                    (PDF, Word, Excel). Only files with a real selectable text layer are
                    captured &mdash; scanned drawings with no text layer are not indexed
                    and would need OCR, which this does not do. Nothing leaves this
                    browser; no original files are stored, only extracted text.
                </div>
                <label style="display:flex; align-items:center; gap:7px; margin-bottom:10px; cursor:pointer;">
                    <input id="sdx-index-enabled-toggle" type="checkbox">
                    <span>Enable automatic content indexing</span>
                </label>
                <div style="
                    display:flex;
                    justify-content:space-between;
                    gap:10px;
                    margin-bottom:10px;
                    font-size:12px;
                    background:#f8f8f8;
                    border:1px solid #ddd;
                    border-radius:6px;
                    padding:8px;
                ">
                    <div>Documents indexed: <b id="sdx-index-doc-count">-</b></div>
                    <div>Storage used: <b id="sdx-index-storage-used">-</b></div>
                </div>
                <label for="sdx-index-doc-limit" style="display:block; margin-bottom:3px;">
                    Keep at most this many documents (oldest removed automatically):
                </label>
                <div style="display:flex; gap:6px; margin-bottom:10px;">
                    <input id="sdx-index-doc-limit"
                           type="number"
                           min="1"
                           step="1"
                           style="
                               width:150px;
                               padding:6px;
                               border:1px solid #aaa;
                               border-radius:4px;
                           ">
                    <button id="sdx-index-save-limit"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#0078d4;
                                color:white;
                                border:none;
                                border-radius:4px;
                            ">
                        Save Limit
                    </button>
                </div>
                <label for="sdx-index-purge-count" style="display:block; margin-bottom:3px;">
                    Purge this many of the oldest indexed documents:
                </label>
                <div style="display:flex; gap:6px; margin-bottom:6px;">
                    <input id="sdx-index-purge-count"
                           type="number"
                           min="0"
                           step="1"
                           value="0"
                           style="
                               width:150px;
                               padding:6px;
                               border:1px solid #aaa;
                               border-radius:4px;
                           ">
                    <button id="sdx-index-purge-run"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#a4262c;
                                color:white;
                                border:none;
                                border-radius:4px;
                            ">
                        Purge
                    </button>
                </div>
                <div id="sdx-index-purge-estimate" style="font-size:11px; color:#666; margin-bottom:10px;">
                    Estimated space freed: 0 B
                </div>
                <div style="display:flex; gap:6px; margin-bottom:6px;">
                    <button id="sdx-index-purge-all"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#5c0009;
                                color:white;
                                border:none;
                                border-radius:4px;
                            ">
                        Purge All Indexed Documents
                    </button>
                </div>
                <div style="font-size:11px; color:#666; margin-bottom:10px;">
                    Deletes the entire local content index, not just the oldest documents. Asks for confirmation
                    twice before deleting anything.
                </div>
                <hr style="border:none; border-top:1px solid #ddd; margin:4px 0 10px;">
                <label for="sdx-index-search-text" style="display:block; margin-bottom:3px;">
                    Search indexed document text:
                </label>
                <div style="display:flex; gap:6px; margin-bottom:8px;">
                    <input id="sdx-index-search-text"
                           type="text"
                           placeholder="Example: mix design, transformer, XFMR..."
                           style="
                               flex:1;
                               min-width:0;
                               padding:6px;
                               border:1px solid #aaa;
                               border-radius:4px;
                           ">
                    <button id="sdx-index-search-run"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#8764b8;
                                color:white;
                                border:none;
                                border-radius:4px;
                                flex-shrink:0;
                            ">
                        Search
                    </button>
                </div>
                <div id="sdx-index-search-results"
                     style="
                         max-height:220px;
                         overflow-y:auto;
                         border:1px solid #ddd;
                         border-radius:6px;
                         padding:2px;
                     "></div>
            </div>
            <div id="sdx-settings-tab-content" style="display:none;">
                <label for="sdx-settings-default-project" style="display:block; margin-bottom:3px;">
                    Project to search (always used once set, overriding whatever SDx's own page looks like it's
                    showing - select "No default set" to auto-detect instead):
                </label>
                <div style="display:flex; gap:6px; margin-bottom:14px;">
                    <select id="sdx-settings-default-project"
                            style="
                                flex:1;
                                min-width:0;
                                padding:6px;
                                border:1px solid #aaa;
                                border-radius:4px;
                            ">
                        <option value="">No default set</option>
                    </select>
                    <button id="sdx-settings-save-default-project"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#0078d4;
                                color:white;
                                border:none;
                                border-radius:4px;
                                flex-shrink:0;
                            ">
                        Save
                    </button>
                </div>
                <hr style="border:none; border-top:1px solid #ddd; margin:4px 0 12px;">
                <label for="sdx-settings-panel-width" style="display:block; margin-bottom:3px;">
                    Popup width (px):
                </label>
                <div style="display:flex; gap:6px; margin-bottom:12px;">
                    <input id="sdx-settings-panel-width"
                           type="number"
                           min="${MIN_PANEL_WIDTH_PX}"
                           max="${MAX_PANEL_WIDTH_PX}"
                           step="10"
                           style="
                               width:150px;
                               padding:6px;
                               border:1px solid #aaa;
                               border-radius:4px;
                           ">
                    <button id="sdx-settings-save-width"
                            style="
                                padding:6px 12px;
                                cursor:pointer;
                                background:#0078d4;
                                color:white;
                                border:none;
                                border-radius:4px;
                            ">
                        Save Width
                    </button>
                </div>
                <hr style="border:none; border-top:1px solid #ddd; margin:4px 0 12px;">
                <label style="display:flex; align-items:center; gap:7px; margin-bottom:8px; cursor:pointer;">
                    <input id="sdx-settings-autoclose-enabled" type="checkbox">
                    <span>Automatically close this popup after inactivity</span>
                </label>
                <div style="display:flex; align-items:center; gap:6px; margin-bottom:14px;">
                    <span>Close after</span>
                    <input id="sdx-settings-autoclose-seconds"
                           type="number"
                           min="5"
                           step="5"
                           style="
                               width:80px;
                               padding:6px;
                               border:1px solid #aaa;
                               border-radius:4px;
                           ">
                    <span>seconds of no activity in the popup</span>
                </div>
                <label style="display:flex; align-items:flex-start; gap:7px; cursor:pointer;">
                    <input id="sdx-settings-close-on-outside-click" type="checkbox" style="margin-top:2px;">
                    <span>Close this popup when clicking anywhere inside SDx (outside the popup)</span>
                </label>
                <div style="font-size:11px; color:#666; margin-top:10px; line-height:1.35;">
                    These two are independent - either, both, or neither can be on. Checkbox changes here save immediately.
                </div>
            </div>
        `;
        panel.style.cssText = `
            position: fixed;
            bottom: 78px;
            right: ${RIGHT_OFFSET}px;
            z-index: 999999;
            background: #ffffff;
            border: 1px solid #999;
            box-shadow: 0 4px 16px rgba(0,0,0,0.35);
            padding: 12px;
            font-family: Arial, sans-serif;
            font-size: 13px;
            color: #222;
            border-radius: 8px;
            width: ${getPanelWidthPx()}px;
            box-sizing: border-box;
            display: none;
        `;
        document.body.appendChild(panel);
        restoreSavedUiValues();
        wireEvents();
        updateGenericFilterVisibility();
    }
    function applyPanelWidth() {
        const panel = document.getElementById('sdx-search-helper');
        if (panel) panel.style.width = getPanelWidthPx() + 'px';
    }
    // ============================================================
    // UI builders
    // ============================================================
    function buildProjectBaseOptionsHtml() {
        const bases = getSearchBases();
        // Hides any stale/corrupted keys saved by older versions of this
        // script (e.g. from the /dashboards "selected=" bug) without
        // touching the underlying storage.
        const keys = Object.keys(bases).filter(isLikelyValidProjectKey);
        const currentKey = getCurrentProjectKey();
        // Preferred is the single "Project to search" setting from the
        // Settings tab - once set, it always wins here, regardless of what
        // the current page looks like. It used to only apply when the
        // current page didn't clearly indicate a project, gated behind a
        // separate "force" checkbox that was easy to forget to also turn
        // on - now that checkbox is gone and setting a default just means
        // "always use this one."
        const preferredKey = GM_getValue('sdxPreferredProjectKey', '');
        const lastActive = GM_getValue('sdxLastActiveProjectKey', '');
        if (keys.length === 0) {
            return '<option value="">No saved search base yet</option>';
        }
        return keys.map(key => {
            const selected = preferredKey
                ? key === preferredKey
                : (currentKey ? key === currentKey : key === lastActive);
            return `<option value="${escapeHtml(key)}" ${selected ? 'selected' : ''}>${escapeHtml(key)}</option>`;
        }).join('');
    }
    function refreshProjectBaseDropdown() {
        const selector = document.getElementById('sdx-project-base');
        if (!selector) return;
        // buildProjectBaseOptionsHtml() already marks the correct <option>
        // as selected (preferred default > current page > last active) -
        // this used to then immediately override that with .value =
        // currentKey whenever currentKey was truthy, which silently stomped
        // on a correctly-set default (or any other fallback) every time the
        // panel reopened. Setting innerHTML alone is enough; no follow-up
        // override needed.
        selector.innerHTML = buildProjectBaseOptionsHtml();
    }
    function buildDisciplineCheckboxHtml() {
        return DISCIPLINE_CODES.map(code => {
            const checked = Array.isArray(savedDisciplines) && savedDisciplines.includes(code)
                ? 'checked'
                : '';
            return `
                <label style="
                    display:inline-flex;
                    align-items:center;
                    gap:4px;
                    width:52px;
                    margin-bottom:5px;
                    cursor:pointer;
                ">
                    <input type="checkbox"
                           class="sdx-discipline-checkbox"
                           value="${escapeHtml(code)}"
                           ${checked}>
                    <span>${escapeHtml(code)}</span>
                </label>
            `;
        }).join('');
    }
    function restoreSavedUiValues() {
        document.getElementById('sdx-heuristic').value = savedHeuristic;
        document.getElementById('sdx-contract-field').value = savedContractField;
        document.getElementById('sdx-contract-value').value = savedContractValue;
        document.getElementById('sdx-generic-filter-type').value = savedGenericFilterType;
        document.getElementById('sdx-issue-date').value = savedIssueDate;
        document.getElementById('sdx-status').value = savedStatus;
        document.getElementById('sdx-wp-contract').value = savedWpContract;
        document.getElementById('sdx-wp-need-send-out').checked = !!savedWpNeedSendOut;
        document.getElementById('sdx-index-enabled-toggle').checked = !!GM_getValue('sdxIndexEnabled', true);
        document.getElementById('sdx-index-doc-limit').value =
            Number(GM_getValue('sdxIndexDocLimit', DEFAULT_INDEX_DOC_LIMIT)) || DEFAULT_INDEX_DOC_LIMIT;
        document.getElementById('sdx-settings-panel-width').value = getPanelWidthPx();
        document.getElementById('sdx-settings-autoclose-enabled').checked = !!GM_getValue('sdxAutoCloseEnabled', false);
        document.getElementById('sdx-settings-autoclose-seconds').value =
            Number(GM_getValue('sdxAutoCloseSeconds', DEFAULT_AUTO_CLOSE_SECONDS)) || DEFAULT_AUTO_CLOSE_SECONDS;
        document.getElementById('sdx-settings-close-on-outside-click').checked = !!GM_getValue('sdxCloseOnOutsideClick', false);
        // No follow-up override of the project dropdown here - its <option>
        // elements already have the correct one marked selected (see
        // buildProjectBaseOptionsHtml(), used when the panel's innerHTML was
        // built above). Forcing .value = currentKey afterward used to stomp
        // on that - a correctly-set default project would get silently
        // replaced by whatever getCurrentProjectKey() detected, which is
        // exactly what made the default feel like it "wasn't being properly
        // set."
    }
    function wireEvents() {
        document.getElementById('sdx-close-panel').addEventListener('click', hidePanel);
        document.getElementById('sdx-tab-search').addEventListener('click', showSearcherTab);
        document.getElementById('sdx-tab-work-package').addEventListener('click', showWorkPackageTab);
        document.getElementById('sdx-tab-index').addEventListener('click', showIndexTab);
        document.getElementById('sdx-tab-settings').addEventListener('click', showSettingsTab);
        document.getElementById('sdx-settings-save-default-project').addEventListener('click', saveSettingsDefaultProject);
        document.getElementById('sdx-settings-save-width').addEventListener('click', saveSettingsPanelWidth);
        document.getElementById('sdx-settings-autoclose-enabled').addEventListener('change', saveSettingsAutoCloseEnabled);
        document.getElementById('sdx-settings-autoclose-seconds').addEventListener('change', saveSettingsAutoCloseSeconds);
        document.getElementById('sdx-settings-close-on-outside-click').addEventListener('change', saveSettingsCloseOnOutsideClick);
        document.getElementById('sdx-save-current-base').addEventListener('click', setCurrentPageAsSearchBase);
        // A manual pick here is immediate, explicit intent - remember it as
        // the last-active project right away, so it's still respected the
        // next time the panel opens (when no Settings default is pinned),
        // instead of reverting to whatever auto-detection thinks.
        document.getElementById('sdx-project-base').addEventListener('change', function () {
            if (this.value) GM_setValue('sdxLastActiveProjectKey', this.value);
        });
        document.getElementById('sdx-apply-search').addEventListener('click', runSearchFromPanel);
        document.getElementById('sdx-clear-search').addEventListener('click', resetSearcherFormOnly);
        document.getElementById('sdx-wp-apply').addEventListener('click', runWorkPackageHelper);
        document.getElementById('sdx-wp-clear').addEventListener('click', resetWorkPackageFormOnly);
        document.getElementById('sdx-generic-filter-type').addEventListener('change', updateGenericFilterVisibility);
        document.getElementById('sdx-index-enabled-toggle').addEventListener('change', toggleIndexEnabledFromPanel);
        document.getElementById('sdx-index-save-limit').addEventListener('click', saveIndexLimitFromPanel);
        document.getElementById('sdx-index-purge-count').addEventListener('input', updatePurgeEstimateDisplay);
        document.getElementById('sdx-index-purge-run').addEventListener('click', runPurgeOldestFromPanel);
        document.getElementById('sdx-index-purge-all').addEventListener('click', runPurgeAllFromPanel);
        document.getElementById('sdx-index-search-run').addEventListener('click', runIndexTextSearch);
        document.getElementById('sdx-index-search-text').addEventListener('keydown', function (event) {
            if (event.key === 'Enter') runIndexTextSearch();
        });
        document.getElementById('sdx-search-text').addEventListener('keydown', function (event) {
            if (event.key === 'Enter') runSearchFromPanel();
        });
        document.getElementById('sdx-search-text').addEventListener('input', scheduleLiveSearchPreview);
        document.getElementById('sdx-contract-value').addEventListener('keydown', function (event) {
            if (event.key === 'Enter') runSearchFromPanel();
        });
        document.getElementById('sdx-wp-contract').addEventListener('keydown', function (event) {
            if (event.key === 'Enter') runWorkPackageHelper();
        });
        document.addEventListener('keydown', function (event) {
            if (event.ctrlKey && event.shiftKey && event.key.toLowerCase() === 's') {
                event.preventDefault();
                rememberCurrentSearchPageIfApplicable();
                clearSearchTextOnOpen();
                togglePanel();
            }
        });
        const panelEl = document.getElementById('sdx-search-helper');
        if (panelEl) {
            ['mousemove', 'keydown', 'click', 'input'].forEach(evt => {
                panelEl.addEventListener(evt, scheduleAutoCloseTimer);
            });
        }
    }
    function updateGenericFilterVisibility() {
        const type = document.getElementById('sdx-generic-filter-type').value;
        document.getElementById('sdx-issue-date-box').style.display =
            type === 'issueDateNewer' || type === 'issueDateOlder'
                ? 'block'
                : 'none';
        document.getElementById('sdx-discipline-box').style.display =
            type === 'discipline'
                ? 'block'
                : 'none';
        document.getElementById('sdx-status-box').style.display =
            type === 'status'
                ? 'block'
                : 'none';
    }
    // ============================================================
    // Page mode and tabs
    // ============================================================
    function getPageModeMessage() {
        const currentKey = getCurrentProjectKey();
        const bases = getSearchBases();
        const baseCount = Object.keys(bases).length;
        if (currentPageHasQueryFilter()) {
            if (currentKey) {
                return 'Search mode: searchable SDx list. Search base can be saved for project/config: ' + escapeHtml(currentKey);
            }
            return 'Search mode: searchable SDx list. Project/config was not detected.';
        }
        if (currentKey && bases[currentKey]) {
            return 'Search mode: not a list. Saved search base found for current project/config: ' + escapeHtml(currentKey);
        }
        if (baseCount > 0) {
            return 'Search mode: not a list. Select the correct project search base below before searching.';
        }
        return 'Search mode: no saved search base. Open an All Documents list once, then click Set Current Page as Search Base.';
    }
    function currentPageHasQueryFilter() {
        return (window.location.hash || '').includes('queryFilter=');
    }
    const TAB_DEFS = [
        { id: 'search', tabButtonId: 'sdx-tab-search', contentId: 'sdx-search-tab-content', color: '#0078d4', focusId: 'sdx-search-text' },
        { id: 'wp', tabButtonId: 'sdx-tab-work-package', contentId: 'sdx-work-package-tab-content', color: '#107c10', focusId: 'sdx-wp-contract' },
        { id: 'index', tabButtonId: 'sdx-tab-index', contentId: 'sdx-index-tab-content', color: '#8764b8', focusId: 'sdx-index-doc-limit' },
        { id: 'settings', tabButtonId: 'sdx-tab-settings', contentId: 'sdx-settings-tab-content', color: '#605e5c', focusId: 'sdx-settings-panel-width' }
    ];
    function activateTab(tabId) {
        currentTabId = tabId;
        TAB_DEFS.forEach(def => {
            const content = document.getElementById(def.contentId);
            if (content) content.style.display = def.id === tabId ? 'block' : 'none';
            setTabStyle(def.tabButtonId, def.id === tabId, def.color);
        });
        const relevantTab = tabId === 'search' || tabId === 'wp';
        const resultsWrapper = document.getElementById('sdx-search-results-wrapper');
        if (resultsWrapper) {
            resultsWrapper.style.display = (relevantTab && resultsWrapper.dataset.hasContent === '1') ? 'block' : 'none';
        }
        // Redundant to show alongside the Settings tab's own "Default
        // project" selector (and not actionable from the Content Index tab
        // either) - only relevant while actually searching.
        const projectBaseBlock = document.getElementById('sdx-project-base-block');
        if (projectBaseBlock) {
            projectBaseBlock.style.display = relevantTab ? 'block' : 'none';
        }
        if (tabId === 'index') {
            refreshIndexTab();
            return;
        }
        if (tabId === 'settings') {
            refreshSettingsTab();
            return;
        }
        const activeDef = TAB_DEFS.find(def => def.id === tabId);
        const input = activeDef && document.getElementById(activeDef.focusId);
        if (input) input.focus();
    }
    function showSearcherTab() { activateTab('search'); }
    function showWorkPackageTab() { activateTab('wp'); }
    function showIndexTab() { activateTab('index'); }
    function showSettingsTab() { activateTab('settings'); }
    function setTabStyle(id, active, activeColor) {
        const button = document.getElementById(id);
        if (!button) return;
        if (active) {
            button.style.background = activeColor;
            button.style.color = 'white';
            button.style.border = 'none';
        } else {
            button.style.background = '#f3f3f3';
            button.style.color = '#222';
            button.style.border = '1px solid #bbb';
        }
    }
    function clearSearchTextOnOpen() {
        const input = document.getElementById('sdx-search-text');
        if (input) input.value = '';
    }
    function togglePanel() {
        const panel = document.getElementById('sdx-search-helper');
        if (!panel) return;
        panel.style.display =
            panel.style.display === 'none' || panel.style.display === ''
                ? 'block'
                : 'none';
        if (panel.style.display === 'block') {
            refreshProjectBaseDropdown();
            const status = document.getElementById('sdx-page-status');
            if (status) status.innerHTML = getPageModeMessage();
            const activeDef = TAB_DEFS.find(def => def.id === currentTabId) || TAB_DEFS[0];
            const input = document.getElementById(activeDef.focusId);
            if (input) input.focus();
            scheduleAutoCloseTimer();
        } else {
            clearAutoCloseTimer();
        }
    }
    function hidePanel() {
        const panel = document.getElementById('sdx-search-helper');
        if (panel) panel.style.display = 'none';
        clearAutoCloseTimer();
        if (liveSearchDebounceId) {
            clearTimeout(liveSearchDebounceId);
            liveSearchDebounceId = null;
        }
    }
    // ============================================================
    // Settings: default project
    // ============================================================
    function refreshSettingsTab() {
        const select = document.getElementById('sdx-settings-default-project');
        if (select) {
            const bases = getSearchBases();
            const keys = Object.keys(bases).filter(isLikelyValidProjectKey);
            const preferred = GM_getValue('sdxPreferredProjectKey', '');
            select.innerHTML = '<option value="">No default set</option>' +
                keys.map(key => `<option value="${escapeHtml(key)}" ${key === preferred ? 'selected' : ''}>${escapeHtml(key)}</option>`).join('');
        }
        document.getElementById('sdx-settings-panel-width').value = getPanelWidthPx();
        document.getElementById('sdx-settings-autoclose-enabled').checked = !!GM_getValue('sdxAutoCloseEnabled', false);
        document.getElementById('sdx-settings-autoclose-seconds').value =
            Number(GM_getValue('sdxAutoCloseSeconds', DEFAULT_AUTO_CLOSE_SECONDS)) || DEFAULT_AUTO_CLOSE_SECONDS;
        document.getElementById('sdx-settings-close-on-outside-click').checked = !!GM_getValue('sdxCloseOnOutsideClick', false);
        const widthInput = document.getElementById('sdx-settings-panel-width');
        if (widthInput) widthInput.focus();
    }
    function saveSettingsDefaultProject() {
        const select = document.getElementById('sdx-settings-default-project');
        GM_setValue('sdxPreferredProjectKey', select ? select.value : '');
        refreshProjectBaseDropdown();
    }
    // ============================================================
    // Settings: panel width + auto-close behavior
    // ============================================================
    function saveSettingsPanelWidth() {
        const input = document.getElementById('sdx-settings-panel-width');
        const value = Math.min(MAX_PANEL_WIDTH_PX, Math.max(MIN_PANEL_WIDTH_PX, parseInt(input.value, 10) || DEFAULT_PANEL_WIDTH_PX));
        input.value = value;
        GM_setValue('sdxPanelWidthPx', value);
        applyPanelWidth();
    }
    function saveSettingsAutoCloseEnabled() {
        const checked = document.getElementById('sdx-settings-autoclose-enabled').checked;
        GM_setValue('sdxAutoCloseEnabled', checked);
        scheduleAutoCloseTimer();
    }
    function saveSettingsAutoCloseSeconds() {
        const input = document.getElementById('sdx-settings-autoclose-seconds');
        const value = Math.max(5, parseInt(input.value, 10) || DEFAULT_AUTO_CLOSE_SECONDS);
        input.value = value;
        GM_setValue('sdxAutoCloseSeconds', value);
        scheduleAutoCloseTimer();
    }
    function saveSettingsCloseOnOutsideClick() {
        const checked = document.getElementById('sdx-settings-close-on-outside-click').checked;
        GM_setValue('sdxCloseOnOutsideClick', checked);
    }
    let autoCloseTimerId = null;
    function clearAutoCloseTimer() {
        if (autoCloseTimerId) {
            clearTimeout(autoCloseTimerId);
            autoCloseTimerId = null;
        }
    }
    function scheduleAutoCloseTimer() {
        clearAutoCloseTimer();
        if (!GM_getValue('sdxAutoCloseEnabled', false)) return;
        const panel = document.getElementById('sdx-search-helper');
        if (!panel || panel.style.display !== 'block') return;
        const seconds = Number(GM_getValue('sdxAutoCloseSeconds', DEFAULT_AUTO_CLOSE_SECONDS)) || DEFAULT_AUTO_CLOSE_SECONDS;
        autoCloseTimerId = setTimeout(hidePanel, seconds * 1000);
    }
    // Global, installed once: closes the popup on a click anywhere else in
    // SDx when that setting is on. Uses the capture phase so it still sees
    // the click even if SDx's own UI stops propagation on it.
    function installOutsideClickHandler() {
        if (window.__sdxOutsideClickInstalled) return;
        window.__sdxOutsideClickInstalled = true;
        document.addEventListener('click', function (event) {
            if (!GM_getValue('sdxCloseOnOutsideClick', false)) return;
            const panel = document.getElementById('sdx-search-helper');
            if (!panel || panel.style.display !== 'block') return;
            if (panel.contains(event.target)) return;
            const sideBarBtn = document.getElementById('side_bar_sdx_searcher_btn');
            const floatingBtn = document.getElementById('sdx-wizard-launcher');
            if (sideBarBtn && sideBarBtn.contains(event.target)) return;
            if (floatingBtn && floatingBtn.contains(event.target)) return;
            hidePanel();
        }, true);
    }
    // ============================================================
    // Search criteria
    // ============================================================
    function collectSearcherCriteria() {
        return {
            type: 'search',
            searchText: document.getElementById('sdx-search-text').value.trim(),
            heuristic: document.getElementById('sdx-heuristic').value,
            contractField: document.getElementById('sdx-contract-field').value,
            contractValue: document.getElementById('sdx-contract-value').value.trim(),
            genericFilterType: document.getElementById('sdx-generic-filter-type').value,
            issueDate: document.getElementById('sdx-issue-date').value,
            disciplines: getSelectedDisciplines(),
            status: document.getElementById('sdx-status').value
        };
    }
    // ============================================================
    // Live search preview (as-you-type)
    //
    // Fires the same instant-preview API call used by Cast Search, but
    // debounced off typing in the search box instead of a button click - so
    // matches start showing up before the user even finishes composing the
    // query. Deliberately does NOT open a new tab or touch SDx's own app at
    // all; that only happens when Cast Search is actually clicked, which is
    // why the preview footer here always reminds the user of that.
    // ============================================================
    let liveSearchDebounceId = null;
    function clearLiveSearchPreview() {
        if (liveSearchDebounceId) {
            clearTimeout(liveSearchDebounceId);
            liveSearchDebounceId = null;
        }
        const wrapper = document.getElementById('sdx-search-results-wrapper');
        if (wrapper) {
            wrapper.style.display = 'none';
            wrapper.dataset.hasContent = '0';
        }
    }
    function scheduleLiveSearchPreview() {
        if (liveSearchDebounceId) clearTimeout(liveSearchDebounceId);
        liveSearchDebounceId = setTimeout(runLiveSearchPreview, LIVE_SEARCH_DEBOUNCE_MS);
    }
    function runLiveSearchPreview() {
        const input = document.getElementById('sdx-search-text');
        if (!input) return;
        if (input.value.trim().length < LIVE_SEARCH_MIN_CHARS) {
            // Too short to be worth a request - and if a longer preview was
            // showing a moment ago, clear it so it doesn't look stale.
            const wrapper = document.getElementById('sdx-search-results-wrapper');
            if (wrapper) {
                wrapper.style.display = 'none';
                wrapper.dataset.hasContent = '0';
            }
            return;
        }
        const criteria = collectSearcherCriteria();
        runDirectApiSearch(criteria, { isLivePreview: true });
    }
    function runSearchFromPanel() {
        const criteria = collectSearcherCriteria();
        GM_setValue('sdxHeuristic', criteria.heuristic);
        GM_setValue('sdxContractField', criteria.contractField);
        GM_setValue('sdxContractValue', criteria.contractValue);
        GM_setValue('sdxGenericFilterType', criteria.genericFilterType);
        GM_setValue('sdxIssueDate', criteria.issueDate);
        GM_setValue('sdxDisciplines', criteria.disciplines);
        GM_setValue('sdxStatus', criteria.status);
        runCastSearchHybrid(criteria);
    }
    function getSelectedDisciplines() {
        return Array.from(document.querySelectorAll('.sdx-discipline-checkbox:checked'))
            .map(cb => cb.value);
    }
    function runWorkPackageHelper() {
        const contract = document.getElementById('sdx-wp-contract').value.trim();
        const needSendOut = document.getElementById('sdx-wp-need-send-out').checked;
        if (!contract) {
            alert('Enter a contract number first.');
            return;
        }
        GM_setValue('sdxWpContract', contract);
        GM_setValue('sdxWpNeedSendOut', needSendOut);
        runCastSearchHybrid({
            type: 'workPackage',
            contract: contract,
            needSendOut: needSendOut
        });
    }
    // ============================================================
    // Hybrid search: instant in-panel preview + real SDx tab
    //
    // Runs both at once: castSearchInNewTab() opens the actual SDx results
    // in a new tab (the real, interactive native grid, for bulk actions like
    // downloading PDFs via SDx's own Actions tab), while runDirectApiSearch()
    // independently calls SDx's own search API directly and renders an
    // instant preview right here in the panel - no page load needed for
    // that part. The preview always makes clear whether the full results
    // are actually on their way in a new tab, so it's never mistaken for
    // the complete picture.
    // ============================================================
    function runCastSearchHybrid(criteria) {
        const newTabOpened = castSearchInNewTab(criteria);
        runDirectApiSearch(criteria, { newTabOpened: newTabOpened });
    }
    // ============================================================
    // Cast Search / Work Package Helper: open results in a real SDx tab
    //
    // Per explicit request: results should show up in SDx's own native grid
    // (not this panel), in a brand-new tab, so the user can act on them with
    // SDx's own tools (e.g. the Actions tab to bulk-download PDFs). Always
    // opens a new tab - even if the current tab already happens to be on a
    // results list - so whatever the user was already doing there is left
    // undisturbed. The new tab bootstraps on a clean, hash-stripped URL
    // first (see the warm-up fix notes below for why a cold deep link fails
    // auth), then this script - running fresh in that new tab - navigates
    // straight to the FINAL filtered results (built up front by
    // buildFinalTargetUrl(), see below) via checkForPendingWarmup(), while
    // checkForPendingResultsOverlay() independently surfaces any local
    // content-index matches on top of it. Returns true if a new tab was
    // actually opened, false if it bailed out (no saved search base yet) -
    // the hybrid preview above uses that to tell the user honestly whether
    // full results are really on their way.
    // ============================================================
    function castSearchInNewTab(criteria) {
        rememberCurrentSearchPageIfApplicable();
        const projectKey = getBestProjectKeyForSearch() || getCurrentProjectKey();
        const bases = getSearchBases();
        if (!projectKey || !bases[projectKey]) {
            alert(
                'SDx Searcher does not have a saved search base for this project yet.\n\n' +
                'Open this project\'s All Documents list once, then click "Set Current Page as Search Base".\n\n' +
                'If you already saved multiple projects, select the correct project search base in the dropdown.'
            );
            return false;
        }
        const finalUrl = buildFinalTargetUrl(criteria, projectKey);
        if (!finalUrl) {
            alert('Could not build a filtered SDx URL from the saved search base for this project. Try re-saving the search base from a working All Documents list.');
            return false;
        }
        // Stash the criteria + projectKey so that as soon as this new tab's
        // script runs - even on the plain bootstrap page, before SDx's own
        // app has finished loading - checkForPendingResultsOverlay() can
        // independently fire the same instant-preview API call plus a local
        // content-index check, and show them together as a popup right in
        // this tab. That's what actually solves the preview getting "left
        // behind" on the original tab: put it where the focus goes instead.
        GM_setValue('sdxPendingResultsOverlay', {
            created: Date.now(),
            criteria: criteria,
            projectKey: projectKey
        });
        // Open a clean, hash-stripped URL first so SDx can log in / bootstrap
        // normally in the new tab. Once that tab is authenticated, this
        // script (running fresh there) navigates on directly to the final
        // filtered URL - not the stale saved-base filter - which is what
        // checkForPendingWarmup() handles on that page's init. That saves an
        // entire extra reload compared to landing on the old saved filter
        // first and only then swapping in the real criteria.
        savePendingWarmup(projectKey, finalUrl);
        window.open(stripHashFromUrl(bases[projectKey]), '_blank');
        return true;
    }
    // ============================================================
    // Build the final SDx results URL up front
    //
    // Previously, the new tab first landed on whatever filter was saved as
    // the project's search base, and only then swapped in the real criteria
    // on a second reload. Since the real criteria are already known before
    // the tab even opens, the actual target queryFilter can be built right
    // now instead - by reusing the saved base URL's own hash (so its
    // entityType/config/selected/title stay intact) and swapping in a fresh
    // queryFilter built from the current criteria. That skips landing on the
    // stale filter entirely: one less full page load in the new tab.
    // ============================================================
    function buildFinalTargetUrl(criteria, projectKey) {
        const bases = getSearchBases();
        const baseUrl = bases[projectKey];
        if (!baseUrl) return null;
        let hash = '';
        try {
            hash = new URL(baseUrl).hash || '';
        } catch (error) {
            const hashIndex = baseUrl.indexOf('#');
            hash = hashIndex === -1 ? '' : baseUrl.slice(hashIndex);
        }
        if (!hash.includes('queryFilter=')) return null;
        const existingFilter = getExistingQueryFilter(hash);
        const andGroups = buildAndGroupsFromCriteria(criteria);
        if (andGroups.length === 0) {
            andGroups.push(buildWildcardGroup());
        }
        const filterObject = buildFilterObject(andGroups, existingFilter);
        const encodedFilter = encodeURIComponent(JSON.stringify(filterObject));
        const newHash = hash.replace(/queryFilter=[^;]*/, 'queryFilter=' + encodedFilter);
        return stripHashFromUrl(baseUrl) + newHash;
    }
    // NOTE: not currently called from anywhere (castSearchInNewTab builds the
    // final URL up front instead of editing the current tab's hash) - kept
    // as-is in case a same-tab, no-new-tab apply is ever wanted again.
    function applyCriteriaOnCurrentList(criteria) {
        // Stash the free-text search (if any) so that once the page below
        // reloads onto the real results view, something reading
        // sdxPendingIndexOverlaySearch could re-open the local content index
        // (IndexedDB is shared across every tab on this origin, so this
        // works regardless of which tab actually captured each document) and
        // surface any text-content matches SDx's own metadata search would
        // never see. (checkForPendingResultsOverlay() is the current version
        // of that idea, fed by castSearchInNewTab() instead of this function.)
        if (criteria && criteria.type === 'search' && criteria.searchText && criteria.searchText !== '*') {
            GM_setValue('sdxPendingIndexOverlaySearch', {
                created: Date.now(),
                searchText: criteria.searchText
            });
        }
        const existingFilter = getExistingQueryFilter();
        const andGroups = buildAndGroupsFromCriteria(criteria);
        if (andGroups.length === 0) {
            andGroups.push(buildWildcardGroup());
        }
        const filterObject = buildFilterObject(andGroups, existingFilter);
        updateCurrentHashQueryFilter(filterObject);
    }
    // ============================================================
    // Results overlay on the new tab: instant API preview + content index
    //
    // Per explicit request: since the new tab always steals focus away from
    // the panel showing the instant preview, put that preview (plus any
    // local content-index matches) on the new tab itself instead, as a
    // dismissible popup - so it's visible wherever the user actually ends up
    // looking. This fires on every page load in that tab (bootstrap page
    // included), not just once the final filtered results have loaded,
    // because the preview fetch itself doesn't depend on SDx's own app being
    // ready at all - it can genuinely show up before the real grid does, not
    // after. It re-shows itself on each subsequent reload (bootstrap -> final
    // results) until the user dismisses it or it goes stale, rather than
    // being consumed/cleared after one appearance.
    // ============================================================
    function checkForPendingResultsOverlay() {
        const pending = GM_getValue('sdxPendingResultsOverlay', null);
        if (!pending || !pending.criteria) return;
        const age = Date.now() - (pending.created || 0);
        if (age > PENDING_SEARCH_MAX_AGE_MS) {
            GM_setValue('sdxPendingResultsOverlay', null);
            return;
        }
        showResultsOverlay(pending.criteria, pending.projectKey);
    }
    function showResultsOverlay(criteria, projectKeyHint) {
        if (document.getElementById('sdx-results-overlay')) return;
        const overlay = document.createElement('div');
        overlay.id = 'sdx-results-overlay';
        // A flex column, not a plain scrolling box: the header (with the
        // close button) is a fixed, non-shrinking row, and only the body
        // below it scrolls. That way the close button stays reachable no
        // matter how many items show up and how long the list gets.
        overlay.style.cssText = `
            position: fixed;
            bottom: 20px;
            left: 50%;
            transform: translateX(-50%);
            z-index: 1000000;
            background: #ffffff;
            border: 1px solid #8764b8;
            box-shadow: 0 6px 24px rgba(0,0,0,0.4);
            border-radius: 8px;
            padding: 14px;
            width: 460px;
            max-width: 90vw;
            max-height: 70vh;
            display: flex;
            flex-direction: column;
            box-sizing: border-box;
            font-family: Arial, sans-serif;
            font-size: 13px;
            color: #222;
        `;
        overlay.innerHTML = `
            <div style="display:flex; justify-content:space-between; align-items:flex-start; gap:8px; margin-bottom:8px; flex-shrink:0;">
                <div style="font-weight:700;">🕵️ Instant preview while SDx loads</div>
                <button id="sdx-results-overlay-close"
                        title="Close"
                        style="border:none; background:transparent; font-size:16px; cursor:pointer; color:#555; flex-shrink:0;">✕</button>
            </div>
            <div id="sdx-results-overlay-scroll" style="overflow-y:auto; flex:1 1 auto; min-height:0;">
                <div id="sdx-results-overlay-preview" style="margin-bottom:6px;">
                    <div style="padding:8px; font-size:12px; color:#666;">Loading instant preview...</div>
                </div>
                <div id="sdx-results-overlay-index"></div>
            </div>
        `;
        document.body.appendChild(overlay);
        function dismissOverlay() {
            // Dismissing means "I've seen it" - don't make it reappear on the
            // next reload in this same flow (e.g. bootstrap -> final results).
            GM_setValue('sdxPendingResultsOverlay', null);
            overlay.remove();
            document.removeEventListener('click', handleOutsideClick, true);
        }
        // Per explicit request: clicking anywhere in the page content
        // dismisses this popup, same idea as the main panel's own
        // close-on-outside-click setting (but unconditional here, not gated
        // behind that setting - this is a transient popup, not the panel).
        function handleOutsideClick(event) {
            if (overlay.contains(event.target)) return;
            dismissOverlay();
        }
        document.getElementById('sdx-results-overlay-close').addEventListener('click', dismissOverlay);
        document.addEventListener('click', handleOutsideClick, true);
        fetchDirectApiPreview(criteria, projectKeyHint).then(result => {
            const target = document.getElementById('sdx-results-overlay-preview');
            if (!target) return;
            if (!result.ok) {
                target.innerHTML = `<div style="padding:8px; font-size:12px; color:#a4262c;">${escapeHtml(describePreviewFailure(result))}</div>`;
                return;
            }
            if (!result.items || result.items.length === 0) {
                target.innerHTML = '<div style="padding:8px; font-size:12px; color:#666;">No matching documents found in this preview.</div>';
                return;
            }
            target.innerHTML = buildDirectResultsItemsHtml(result.items, result.projectKey);
        });
        if (criteria && criteria.type === 'search' && criteria.searchText && criteria.searchText !== '*') {
            idbGetAllDocuments().then(documents => {
                const matches = searchIndexedDocuments(documents, criteria.searchText);
                const target = document.getElementById('sdx-results-overlay-index');
                if (!target || matches.length === 0) return; // say nothing if no local matches - keep it uncluttered
                target.innerHTML = `
                    <hr style="border:none; border-top:1px solid #ddd; margin:6px 0 8px;">
                    <div style="font-size:12px; color:#555; margin-bottom:6px; line-height:1.4;">
                        Your local content index also found <b>${matches.length}</b> document${matches.length === 1 ? '' : 's'}
                        whose text matches &ldquo;${escapeHtml(criteria.searchText)}&rdquo;.
                    </div>
                    <div style="max-height:220px; overflow-y:auto; border:1px solid #ddd; border-radius:6px;">
                        ${buildIndexResultsHtml(matches)}
                    </div>
                `;
                wireIndexResultLinks(target);
            }).catch(error => {
                console.warn('SDx Searcher: Could not check content index for overlay.', error);
            });
        }
    }
    function buildAndGroupsFromCriteria(criteria) {
        if (!criteria || !criteria.type) return [];
        if (criteria.type === 'workPackage') {
            return buildWorkPackageGroups(criteria);
        }
        return buildSearcherGroups(criteria);
    }
    function buildSearcherGroups(criteria) {
        const settings = getHeuristicSettings(criteria.heuristic);
        const andGroups = [];
        if (criteria.searchText && criteria.searchText !== '*') {
            const searchGroup = buildSearchGroup(
                settings.fields,
                criteria.searchText,
                settings.operator,
                settings.termMode
            );
            if (searchGroup) andGroups.push(searchGroup);
        }
        if (criteria.contractField && criteria.contractValue) {
            andGroups.push({
                logic: 'and',
                field: criteria.contractField,
                operator: 'contains',
                value: criteria.contractValue
            });
        }
        const genericFilterGroup = buildGenericFilterGroup(criteria);
        if (genericFilterGroup) {
            andGroups.push(genericFilterGroup);
        }
        return andGroups;
    }
    function buildWorkPackageGroups(criteria) {
        const andGroups = [];
        andGroups.push({
            logic: 'and',
            field: 'To_Contract',
            operator: 'contains',
            value: criteria.contract
        });
        if (criteria.needSendOut) {
            andGroups.push({
                logic: 'and',
                field: 'Transmittal',
                operator: 'doesnotcontain',
                value: criteria.contract
            });
        }
        return andGroups;
    }
    // ============================================================
    // OData filter translation (for the direct API search below)
    //
    // Same criteria, same field names as the Kendo-style builder above,
    // just expressed the way the confirmed live request expresses them:
    // contains(Field,'*text') / Field eq 'text' / not contains(...),
    // joined with "and"/"or". Mirrors the leading "*" the native UI itself
    // sends before each term, even though contains() doesn't need it, to
    // stay as close as possible to what's known to work.
    //
    // NOT translated here: the Issue Date newer/older generic filter. The
    // exact OData date-literal format this endpoint expects hasn't been
    // confirmed against a real request, and guessing wrong risks silently
    // sending a broken filter. That one option is skipped for now in the
    // direct-API path; everything else still applies.
    // ============================================================
    function escapeODataString(value) {
        return String(value || '').replace(/'/g, "''");
    }
    function odataContains(field, value, negate) {
        const expr = `contains(${field},'${escapeODataString(value)}')`;
        return negate ? `not ${expr}` : expr;
    }
    function odataEq(field, value) {
        return `${field} eq '${escapeODataString(value)}'`;
    }
    function buildODataOrGroup(fields, value, operator) {
        const parts = fields.map(field => operator === 'eq' ? odataEq(field, value) : odataContains(field, value, false));
        return '(' + parts.join(' or ') + ')';
    }
    function buildODataSearchExpr(criteria) {
        const cleanText = String(criteria.searchText || '').trim();
        if (!cleanText || cleanText === '*') return '';
        const settings = getHeuristicSettings(criteria.heuristic);
        const prefix = value => (settings.operator === 'eq' ? value : '*' + value);
        if (settings.termMode === 'phrase') {
            return buildODataOrGroup(settings.fields, prefix(cleanText), settings.operator);
        }
        const terms = cleanText.split(/\s+/).map(t => t.trim()).filter(Boolean);
        if (terms.length === 0) return '';
        return terms.map(term => buildODataOrGroup(settings.fields, prefix(term), settings.operator)).join(' and ');
    }
    function buildODataFilterFromCriteria(criteria) {
        const groups = [];
        if (criteria && criteria.type === 'workPackage') {
            groups.push(odataContains('To_Contract', criteria.contract, false));
            if (criteria.needSendOut) {
                groups.push(odataContains('Transmittal', criteria.contract, true));
            }
        } else if (criteria) {
            const searchExpr = buildODataSearchExpr(criteria);
            if (searchExpr) groups.push(searchExpr);
            if (criteria.contractField && criteria.contractValue) {
                groups.push(odataContains(criteria.contractField, criteria.contractValue, false));
            }
            if (criteria.genericFilterType === 'discipline' && criteria.disciplines && criteria.disciplines.length > 0) {
                groups.push('(' + criteria.disciplines.map(code => odataEq('Disc', code)).join(' or ') + ')');
            }
            if (criteria.genericFilterType === 'status' && criteria.status) {
                groups.push(odataContains('IP_Status', criteria.status, false));
            }
            // issueDateNewer / issueDateOlder intentionally not translated - see note above.
        }
        if (groups.length === 0) {
            return "contains(Name,'*') or contains(Alt_Doc_Name,'*') or contains(Title,'*') or contains(Attached_File,'*')";
        }
        return groups.join(' and ');
    }
    // ============================================================
    // Direct API search - now used as the "instant preview" half of the
    // hybrid search (see runCastSearchHybrid above). Calls SDx's own OData
    // search endpoint directly (confirmed via DevTools), from whatever tab
    // is already open, and renders results right here in the panel with no
    // page load at all - while castSearchInNewTab() separately opens the
    // real, interactive SDx grid in a new tab. This preview can silently
    // come up empty/unavailable (no captured token yet, wrong project, a
    // rejected token, etc.) without blocking the new-tab flow, since the two
    // are entirely independent of each other.
    // ============================================================
    function buildDirectApiUrl(entityType, filterExpr, top) {
        const root = `${window.location.origin}/ENR01Server/api/v2/SDA/${entityType}`;
        const params = new URLSearchParams();
        params.set('$format', 'json');
        params.set('$top', String(top));
        params.set('$filter', filterExpr);
        params.set('$count', 'false');
        params.set('_', String(Date.now()));
        return `${root}?${params.toString()}`;
    }
    function firstNonEmpty(item, names) {
        for (const name of names) {
            if (item && item[name] !== undefined && item[name] !== null && String(item[name]).trim() !== '') {
                return item[name];
            }
        }
        return '';
    }
    function buildScopedDocumentLink(projectKey, docName) {
        // Rather than guess at a per-document deep link from API fields we
        // haven't confirmed, this scopes the existing, known-working list
        // link down to an exact-name match for just this one document. It's
        // a normal <a> the user clicks themselves (a real browser
        // navigation, not a script-driven window.open), which is exactly
        // the case that's worked reliably throughout this script.
        if (!docName) return '';
        const bases = getSearchBases();
        const baseUrl = bases[projectKey];
        if (!baseUrl) return '';
        const filterObject = buildFilterObject(
            [{ logic: 'and', field: 'Name', operator: 'eq', value: docName }],
            null
        );
        const encodedFilter = encodeURIComponent(JSON.stringify(filterObject));
        const originPath = stripHashFromUrl(baseUrl);
        const configEncoded = encodeURIComponent(JSON.stringify([projectKey]));
        return `${originPath}#/results;queryFilter=${encodedFilter};config=${configEncoded};` +
            `title=${encodeURIComponent('All Documents')};selected=${encodeURIComponent(projectKey)}`;
    }
    function showSearchResultsWrapper() {
        const wrapper = document.getElementById('sdx-search-results-wrapper');
        if (wrapper) {
            wrapper.style.display = 'block';
            wrapper.dataset.hasContent = '1';
        }
    }
    // Always shown above a Cast-Search-triggered preview (never a live-typing
    // one - see buildLiveSearchFooterHtml below) so it can never be mistaken
    // for the complete picture: this panel's list comes from a separate,
    // direct API call and may not exactly match what SDx's own grid returns
    // (different pageSize/paging behavior, for one). newTabOpened tells the
    // user honestly whether the real, interactive SDx results are actually
    // on their way in a new tab, or whether that part failed (no saved
    // search base yet) and this preview is all there is right now.
    function buildNewTabBannerHtml(newTabOpened) {
        if (newTabOpened) {
            return `
                <div style="
                    padding:6px 8px;
                    margin-bottom:6px;
                    font-size:11px;
                    line-height:1.4;
                    background:#eef6ff;
                    border:1px solid #b4d6f7;
                    border-radius:4px;
                    color:#004578;
                ">
                    This is an instant preview. The full, interactive SDx results are loading in a new tab now.
                </div>
            `;
        }
        return `
            <div style="
                padding:6px 8px;
                margin-bottom:6px;
                font-size:11px;
                line-height:1.4;
                background:#fff4ce;
                border:1px solid #e0d48a;
                border-radius:4px;
                color:#5c4813;
            ">
                This is a preview only &mdash; no saved search base yet, so the full SDx results tab could not be opened.
                Use &ldquo;Set Current Page as Search Base&rdquo; once (on a working All Documents list) to enable that.
            </div>
        `;
    }
    // Shown underneath a live-typing preview instead of the new-tab banner -
    // per explicit request, so it's clear this preview updating as you type
    // is not the same thing as actually casting the search.
    function buildLiveSearchFooterHtml() {
        return `
            <div style="
                padding:6px 8px;
                margin-top:6px;
                font-size:11px;
                color:#666;
                border-top:1px solid #eee;
            ">
                Click <b>SDx Search</b> for full SDx results and functionality.
            </div>
        `;
    }
    // Shown only for the live-typing preview, right under the API results
    // and above the "click SDx Search" footer - per explicit request, the
    // live preview should also cover the local content index, not just
    // SDx's own API.
    function buildIndexMatchesSectionHtml(matches) {
        if (!matches || matches.length === 0) return '';
        return `
            <hr style="border:none; border-top:1px solid #ddd; margin:8px 0;">
            <div style="font-size:11px; font-weight:600; color:#8764b8; margin-bottom:4px;">
                Also in your local content index (${matches.length}):
            </div>
            <div>${buildIndexResultsHtml(matches)}</div>
        `;
    }
    function showDirectSearchMessage(message, isError, opts, indexMatches) {
        opts = opts || {};
        const container = document.getElementById('sdx-search-results');
        if (!container) return;
        showSearchResultsWrapper();
        const topBanner = opts.isLivePreview ? '' : buildNewTabBannerHtml(opts.newTabOpened);
        const indexSection = opts.isLivePreview ? buildIndexMatchesSectionHtml(indexMatches) : '';
        const bottomNote = opts.isLivePreview ? buildLiveSearchFooterHtml() : '';
        container.innerHTML = topBanner +
            `<div style="padding:8px; font-size:12px; color:${isError ? '#a4262c' : '#666'};">${escapeHtml(message)}</div>` +
            indexSection + bottomNote;
        if (indexMatches && indexMatches.length > 0) wireIndexResultLinks(container);
    }
    // Shared item-row template used both by the in-panel preview list and by
    // the new-tab results overlay (see showResultsOverlay above), so the two
    // never drift apart.
    function buildDirectResultsItemsHtml(items, projectKey) {
        return items.map(item => {
            const name = firstNonEmpty(item, ['Name', 'Alt_Doc_Name', 'Title', 'Attached_File']) || '(unnamed)';
            const title = firstNonEmpty(item, ['Title']);
            const rev = firstNonEmpty(item, ['Doc_Rev', 'Revision', 'Rev']);
            const status = firstNonEmpty(item, ['IP_Status', 'Status']);
            const issueDate = firstNonEmpty(item, ['Issue_Date']);
            const link = buildScopedDocumentLink(projectKey, firstNonEmpty(item, ['Name']));
            const metaBits = [rev && ('Rev ' + rev), status, issueDate].filter(Boolean).map(escapeHtml).join(' &middot; ');
            return `
                <div style="padding:7px 8px; border-bottom:1px solid #eee; font-size:12px;">
                    ${link
                        ? `<a href="${escapeHtml(link)}" target="_blank" rel="noopener" style="font-weight:600; color:#0078d4; text-decoration:none; word-break:break-word;">${escapeHtml(name)}</a>`
                        : `<span style="font-weight:600; word-break:break-word;">${escapeHtml(name)}</span>`
                    }
                    ${title && title !== name ? `<div style="color:#555; margin-top:2px;">${escapeHtml(title)}</div>` : ''}
                    ${metaBits ? `<div style="color:#888; font-size:11px; margin-top:2px;">${metaBits}</div>` : ''}
                </div>
            `;
        }).join('');
    }
    function renderDirectSearchResults(items, projectKey, opts, indexMatches) {
        opts = opts || {};
        const container = document.getElementById('sdx-search-results');
        if (!container) return;
        showSearchResultsWrapper();
        const topBanner = opts.isLivePreview ? '' : buildNewTabBannerHtml(opts.newTabOpened);
        const indexSection = opts.isLivePreview ? buildIndexMatchesSectionHtml(indexMatches) : '';
        const bottomNote = opts.isLivePreview ? buildLiveSearchFooterHtml() : '';
        const itemsHtml = (!items || items.length === 0)
            ? '<div style="padding:8px; font-size:12px; color:#666;">No matching documents found in this preview.</div>'
            : buildDirectResultsItemsHtml(items, projectKey);
        container.innerHTML = topBanner + itemsHtml + indexSection + bottomNote;
        if (indexMatches && indexMatches.length > 0) wireIndexResultLinks(container);
    }
    // The actual API call, factored out so both the in-panel preview
    // (runDirectApiSearch below) and the new-tab results overlay
    // (showResultsOverlay above) share one implementation instead of two
    // that could drift apart. projectKeyOverride lets a caller pass a known-
    // good project key instead of trying to detect one from the current
    // page - important for the overlay, which may be running on a bare
    // bootstrap page with no route/hash context to read a project from yet.
    async function fetchDirectApiPreview(criteria, projectKeyOverride) {
        const token = getAuthToken();
        if (!token) return { ok: false, reason: 'no-token' };
        const projectKey = projectKeyOverride || getBestProjectKeyForSearch() || getCurrentProjectKey();
        if (!projectKey) return { ok: false, reason: 'no-project' };
        const filterExpr = buildODataFilterFromCriteria(criteria);
        const url = buildDirectApiUrl(DEFAULT_ENTITY_TYPE, filterExpr, 100);
        try {
            const response = await fetch(url, {
                method: 'GET',
                credentials: 'include',
                headers: {
                    accept: 'application/json, text/javascript, */*; q=0.01',
                    authorization: token,
                    spfconfiguid: projectKey
                }
            });
            if (response.status === 401 || response.status === 403) {
                invalidateAuthToken();
                return { ok: false, reason: 'rejected', status: response.status };
            }
            if (!response.ok) {
                return { ok: false, reason: 'http-error', status: response.status, statusText: response.statusText };
            }
            const json = await response.json();
            const items = (json && json.value) || [];
            return { ok: true, items, projectKey };
        } catch (error) {
            console.warn('SDx Searcher: Direct API preview fetch failed.', error);
            return { ok: false, reason: 'network-error' };
        }
    }
    // Only meaningful for free-text search criteria - shared with
    // showResultsOverlay's own equivalent check.
    async function searchContentIndexForCriteria(criteria) {
        if (!criteria || criteria.type !== 'search' || !criteria.searchText || criteria.searchText === '*') return [];
        try {
            const documents = await idbGetAllDocuments();
            return searchIndexedDocuments(documents, criteria.searchText);
        } catch (error) {
            console.warn('SDx Searcher: Could not search content index for live preview.', error);
            return [];
        }
    }
    function describePreviewFailure(result) {
        switch (result.reason) {
            case 'no-token':
                return 'No instant preview available yet - this script hasn\'t captured a session token for a direct API call.';
            case 'no-project':
                return 'Could not determine which project to search for the preview. Pick one in the "Project search base" dropdown first.';
            case 'rejected':
                return 'Instant preview unavailable: session token was rejected (' + result.status + ').';
            case 'http-error':
                return 'Instant preview failed: ' + result.status + ' ' + result.statusText;
            default:
                return 'Instant preview failed due to a network or script error - see the browser console for details.';
        }
    }
    // requestId guards against out-of-order results: live-typing can easily
    // fire several overlapping fetches as the user keeps typing, and without
    // this a slower, older response could land after a newer one and
    // silently overwrite it with stale data.
    let directSearchRequestId = 0;
    // opts.newTabOpened / opts.isLivePreview are purely about what to tell
    // the user (see the banner/footer builders above) - they don't change
    // how this preview itself is fetched or rendered.
    async function runDirectApiSearch(criteria, opts) {
        opts = opts || {};
        const requestId = ++directSearchRequestId;
        rememberCurrentSearchPageIfApplicable();
        showDirectSearchMessage('Loading instant preview...', false, opts);
        // The local content index is only checked for the live-typing
        // preview (a Cast-Search-triggered preview instead gets its
        // content-index matches from the new-tab overlay, once that tab
        // actually opens) - no point paying for an IndexedDB scan otherwise.
        const [result, indexMatches] = await Promise.all([
            fetchDirectApiPreview(criteria),
            opts.isLivePreview ? searchContentIndexForCriteria(criteria) : Promise.resolve([])
        ]);
        if (requestId !== directSearchRequestId) return; // superseded by a newer search/live-typing update
        if (!result.ok) {
            showDirectSearchMessage(describePreviewFailure(result), true, opts, indexMatches);
            return;
        }
        renderDirectSearchResults(result.items, result.projectKey, opts, indexMatches);
    }
    // ============================================================
    // Advanced filters retained
    // ============================================================
    function buildGenericFilterGroup(criteria) {
        switch (criteria.genericFilterType) {
            case 'issueDateNewer':
                if (!criteria.issueDate) return null;
                return {
                    logic: 'and',
                    field: 'Issue_Date',
                    operator: 'gte',
                    value: criteria.issueDate
                };
            case 'issueDateOlder':
                if (!criteria.issueDate) return null;
                return {
                    logic: 'and',
                    field: 'Issue_Date',
                    operator: 'lte',
                    value: criteria.issueDate
                };
            case 'discipline':
                if (!criteria.disciplines || criteria.disciplines.length === 0) return null;
                return {
                    logic: 'or',
                    filters: criteria.disciplines.map(code => ({
                        logic: 'and',
                        field: 'Disc',
                        operator: 'eq',
                        value: code
                    }))
                };
            case 'status':
                if (!criteria.status) return null;
                return {
                    logic: 'and',
                    field: 'IP_Status',
                    operator: 'contains',
                    value: criteria.status
                };
            default:
                return null;
        }
    }
    // ============================================================
    // Filter object
    // ============================================================
    function buildFilterObject(andGroups, existingFilter) {
        return {
            filters: [
                {
                    logic: 'and',
                    filters: andGroups
                }
            ],
            pageSize: existingFilter?.pageSize ?? 100,
            page: 1,
            ignoreQueryBySelectedConfig: existingFilter?.ignoreQueryBySelectedConfig ?? false,
            isLoaded: true,
            ignoreEffectivity: existingFilter?.ignoreEffectivity ?? false,
            returnMarkedForDeleteObjects: existingFilter?.returnMarkedForDeleteObjects ?? false,
            relatedItemFilters: existingFilter?.relatedItemFilters ?? [],
            entityType: existingFilter?.entityType ?? DEFAULT_ENTITY_TYPE
        };
    }
    function buildWildcardGroup() {
        return {
            logic: 'or',
            filters: [
                {
                    logic: 'and',
                    field: 'Name',
                    operator: 'contains',
                    value: '*'
                },
                {
                    logic: 'and',
                    field: 'Alt_Doc_Name',
                    operator: 'contains',
                    value: '*'
                },
                {
                    logic: 'and',
                    field: 'Title',
                    operator: 'contains',
                    value: '*'
                },
                {
                    logic: 'and',
                    field: 'Attached_File',
                    operator: 'contains',
                    value: '*'
                }
            ]
        };
    }
    function updateCurrentHashQueryFilter(filterObject) {
        let hash = window.location.hash || '';
        const encodedFilter = encodeURIComponent(JSON.stringify(filterObject));
        if (!hash.includes('queryFilter=')) {
            alert('Current page does not contain queryFilter. Open a list page or set a search base.');
            return;
        }
        hash = hash.replace(
            /queryFilter=[^;]*/,
            'queryFilter=' + encodedFilter
        );
        window.location.hash = hash;
        setTimeout(() => {
            window.location.reload();
        }, 300);
    }
    // ============================================================
    // Heuristics
    // ============================================================
    function getHeuristicSettings(heuristic) {
        switch (heuristic) {
            case 'broadPhrase':
                return {
                    fields: ['Name', 'Alt_Doc_Name', 'Title', 'Attached_File', 'Originating_Org'],
                    termMode: 'phrase',
                    operator: 'contains'
                };
            case 'documentAllWords':
                return {
                    fields: ['Name', 'Alt_Doc_Name'],
                    termMode: 'allWords',
                    operator: 'contains'
                };
            case 'documentPhrase':
                return {
                    fields: ['Name', 'Alt_Doc_Name'],
                    termMode: 'phrase',
                    operator: 'contains'
                };
            case 'filenameAllWords':
                return {
                    fields: ['Attached_File'],
                    termMode: 'allWords',
                    operator: 'contains'
                };
            case 'filenamePhrase':
                return {
                    fields: ['Attached_File'],
                    termMode: 'phrase',
                    operator: 'contains'
                };
            case 'titleAllWords':
                return {
                    fields: ['Title'],
                    termMode: 'allWords',
                    operator: 'contains'
                };
            case 'titlePhrase':
                return {
                    fields: ['Title'],
                    termMode: 'phrase',
                    operator: 'contains'
                };
            case 'contractAllWords':
                return {
                    fields: ['From_Contract', 'To_Contract'],
                    termMode: 'allWords',
                    operator: 'contains'
                };
            case 'exactDocument':
                return {
                    fields: ['Name', 'Alt_Doc_Name'],
                    termMode: 'phrase',
                    operator: 'eq'
                };
            case 'exactFilename':
                return {
                    fields: ['Attached_File'],
                    termMode: 'phrase',
                    operator: 'eq'
                };
            case 'broadAllWords':
            default:
                // Originating_Org included per explicit request: searching
                // by the originating company (e.g. a vendor/supplier name
                // like "Wartsila") is common enough that it should just work
                // from the plain search box, without the user having to
                // build a separate filter for it every time.
                return {
                    fields: ['Name', 'Alt_Doc_Name', 'Title', 'Attached_File', 'Originating_Org'],
                    termMode: 'allWords',
                    operator: 'contains'
                };
        }
    }
    function buildSearchGroup(fields, searchText, operator, termMode) {
        if (!fields || fields.length === 0) return null;
        const cleanText = String(searchText || '').trim();
        if (!cleanText) return null;
        if (termMode === 'phrase') {
            return {
                logic: 'or',
                filters: fields.map(field => ({
                    logic: 'and',
                    field: field,
                    operator: operator,
                    value: cleanText
                }))
            };
        }
        const terms = cleanText
            .split(/\s+/)
            .map(t => t.trim())
            .filter(Boolean);
        if (terms.length === 0) return null;
        return {
            logic: 'and',
            filters: terms.map(term => ({
                logic: 'or',
                filters: fields.map(field => ({
                    logic: 'and',
                    field: field,
                    operator: operator,
                    value: term
                }))
            }))
        };
    }
    // ============================================================
    // Reset actions
    // ============================================================
    function resetSearcherFormOnly() {
        GM_setValue('sdxHeuristic', 'broadAllWords');
        GM_setValue('sdxContractField', '');
        GM_setValue('sdxContractValue', '');
        GM_setValue('sdxGenericFilterType', '');
        GM_setValue('sdxIssueDate', '');
        GM_setValue('sdxDisciplines', []);
        GM_setValue('sdxStatus', '');
        document.getElementById('sdx-search-text').value = '';
        document.getElementById('sdx-heuristic').value = 'broadAllWords';
        document.getElementById('sdx-contract-field').value = '';
        document.getElementById('sdx-contract-value').value = '';
        document.getElementById('sdx-generic-filter-type').value = '';
        document.getElementById('sdx-issue-date').value = '';
        document.getElementById('sdx-status').value = '';
        document.querySelectorAll('.sdx-discipline-checkbox').forEach(cb => {
            cb.checked = false;
        });
        updateGenericFilterVisibility();
        clearLiveSearchPreview();
        const input = document.getElementById('sdx-search-text');
        if (input) input.focus();
    }
    function resetWorkPackageFormOnly() {
        GM_setValue('sdxWpContract', '');
        GM_setValue('sdxWpNeedSendOut', false);
        document.getElementById('sdx-wp-contract').value = '';
        document.getElementById('sdx-wp-need-send-out').checked = false;
        const input = document.getElementById('sdx-wp-contract');
        if (input) input.focus();
    }
    // ============================================================
    // Query filter reader
    // ============================================================
    // Optional hashOverride lets this parse a hash string other than the
    // current page's own (e.g. a saved search base URL's hash, before ever
    // navigating there) - used by buildFinalTargetUrl() above.
    function getExistingQueryFilter(hashOverride) {
        const hash = hashOverride !== undefined ? (hashOverride || '') : (window.location.hash || '');
        const match = hash.match(/queryFilter=([^;]*)/);
        if (!match || !match[1]) return null;
        try {
            return JSON.parse(decodeURIComponent(match[1]));
        } catch (error) {
            console.warn('SDx Searcher: Could not parse existing queryFilter.', error);
            return null;
        }
    }
    // ============================================================
    // Content index: IndexedDB storage layer
    //
    // Stores extracted plain text only - never the original file bytes -
    // keyed by a document id derived from its request URL. Kept intentionally
    // simple (no full inverted-index structure) since the browser's own
    // IndexedDB + substring/array search over a few hundred-thousand small
    // text records is already fast enough for this use case, and it keeps
    // the storage footprint close to the size of the raw extracted text.
    // ============================================================
    function openIndexDb() {
        return new Promise((resolve, reject) => {
            const request = indexedDB.open(INDEX_DB_NAME, INDEX_DB_VERSION);
            request.onupgradeneeded = () => {
                const db = request.result;
                if (!db.objectStoreNames.contains(INDEX_STORE_NAME)) {
                    const store = db.createObjectStore(INDEX_STORE_NAME, { keyPath: 'id' });
                    store.createIndex('lastAccessedAt', 'lastAccessedAt', { unique: false });
                }
            };
            request.onsuccess = () => resolve(request.result);
            request.onerror = () => reject(request.error);
        });
    }
    function idbGetAllDocuments() {
        return openIndexDb().then(db => new Promise((resolve, reject) => {
            const tx = db.transaction(INDEX_STORE_NAME, 'readonly');
            const request = tx.objectStore(INDEX_STORE_NAME).getAll();
            request.onsuccess = () => resolve(request.result || []);
            request.onerror = () => reject(request.error);
        }));
    }
    function idbPutDocument(record) {
        return openIndexDb().then(db => new Promise((resolve, reject) => {
            const tx = db.transaction(INDEX_STORE_NAME, 'readwrite');
            tx.objectStore(INDEX_STORE_NAME).put(record);
            tx.oncomplete = () => resolve();
            tx.onerror = () => reject(tx.error);
        }));
    }
    function idbDeleteDocuments(ids) {
        if (!ids || ids.length === 0) return Promise.resolve();
        return openIndexDb().then(db => new Promise((resolve, reject) => {
            const tx = db.transaction(INDEX_STORE_NAME, 'readwrite');
            const store = tx.objectStore(INDEX_STORE_NAME);
            ids.forEach(id => store.delete(id));
            tx.oncomplete = () => resolve();
            tx.onerror = () => reject(tx.error);
        }));
    }
    // ============================================================
    // Content index: stats and purge helpers
    // ============================================================
    function estimateRecordSizeBytes(record) {
        const textLength = (record && record.text) ? record.text.length : 0;
        return (textLength * 2) + 200; // UTF-16 code units + a small metadata overhead
    }
    function computeIndexStats(documents) {
        const totalBytes = (documents || []).reduce((sum, doc) => sum + estimateRecordSizeBytes(doc), 0);
        return { count: (documents || []).length, totalBytes };
    }
    function formatBytes(bytes) {
        if (bytes < 1024) return bytes + ' B';
        if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KB';
        if (bytes < 1024 * 1024 * 1024) return (bytes / (1024 * 1024)).toFixed(2) + ' MB';
        return (bytes / (1024 * 1024 * 1024)).toFixed(2) + ' GB';
    }
    function getOldestDocuments(documents, count) {
        const sorted = (documents || []).slice().sort((a, b) => (a.lastAccessedAt || 0) - (b.lastAccessedAt || 0));
        return sorted.slice(0, Math.max(0, count));
    }
    async function enforceIndexDocLimit(limit) {
        const documents = await idbGetAllDocuments();
        if (documents.length <= limit) return;
        const toRemove = getOldestDocuments(documents, documents.length - limit);
        await idbDeleteDocuments(toRemove.map(d => d.id));
    }
    // ============================================================
    // Content index: text extraction
    //
    // PDF extraction uses pdf.js's own text-layer API (no OCR - only text
    // that's already selectable in the PDF gets picked up). DOCX/XLSX
    // extraction unzips the file (they're just zip archives of XML) and
    // strips XML tags out of the relevant document/sheet XML parts - a
    // deliberately lightweight approach since we only need plain text for
    // search, not formatting.
    //
    // NOTE (unverified against the live app): pdf.js's default worker script
    // is loaded from a remote URL, which may or may not be allowed under
    // SDx's own Content-Security-Policy. If it's blocked, PDF extraction for
    // that document silently fails (caught below) rather than breaking
    // anything else - worth confirming once this is tried live.
    // ============================================================
    async function extractTextFromPdf(arrayBuffer) {
        if (typeof pdfjsLib === 'undefined') return '';
        try {
            if (pdfjsLib.GlobalWorkerOptions && !pdfjsLib.GlobalWorkerOptions.workerSrc) {
                pdfjsLib.GlobalWorkerOptions.workerSrc = PDF_WORKER_SRC;
            }
            const pdf = await pdfjsLib.getDocument({ data: arrayBuffer }).promise;
            let text = '';
            for (let pageNum = 1; pageNum <= pdf.numPages; pageNum++) {
                const page = await pdf.getPage(pageNum);
                const content = await page.getTextContent();
                text += content.items.map(item => item.str).join(' ') + '\n';
            }
            return text.trim();
        } catch (error) {
            console.warn('SDx Searcher: PDF text extraction failed.', error);
            return '';
        }
    }
    async function extractTextFromOfficeXml(arrayBuffer, xmlEntryPatterns) {
        if (typeof JSZip === 'undefined') return '';
        try {
            const zip = await JSZip.loadAsync(arrayBuffer);
            const entries = Object.keys(zip.files).filter(name =>
                xmlEntryPatterns.some(pattern => pattern.test(name))
            );
            let combined = '';
            for (const entryName of entries) {
                const xml = await zip.files[entryName].async('string');
                combined += xml.replace(/<[^>]+>/g, ' ') + '\n';
            }
            return combined.replace(/\s+/g, ' ').trim();
        } catch (error) {
            console.warn('SDx Searcher: Office document text extraction failed.', error);
            return '';
        }
    }
    function extractTextFromDocx(arrayBuffer) {
        return extractTextFromOfficeXml(arrayBuffer, [/^word\/document\.xml$/]);
    }
    function extractTextFromXlsx(arrayBuffer) {
        return extractTextFromOfficeXml(arrayBuffer, [/^xl\/sharedStrings\.xml$/, /^xl\/worksheets\/sheet\d+\.xml$/]);
    }
    function guessFileKind(urlOrName, contentType) {
        const lower = (urlOrName || '').split('?')[0].split('#')[0].toLowerCase();
        const type = (contentType || '').toLowerCase();
        if (lower.endsWith('.pdf') || type.includes('pdf')) return 'pdf';
        if (lower.endsWith('.docx') || type.includes('wordprocessingml')) return 'docx';
        if (lower.endsWith('.xlsx') || type.includes('spreadsheetml')) return 'xlsx';
        return null;
    }
    // ============================================================
    // Content index: raw file viewer tabs (the actual capture path)
    //
    // Confirmed against the live app: SDx opens documents by navigating a
    // brand-new tab directly to the file's URL (e.g. .../SPFViewDir/.../
    // Some%20Document.pdf), which the browser's own native PDF viewer then
    // renders. That request never goes through the SPA's in-page fetch/XHR
    // calls, so the capture hooks above never see it - there is nothing for
    // them to intercept. Instead, on a page like this we independently
    // re-request the exact same URL ourselves via GM_xmlhttpRequest (which
    // carries the same session cookies) to get real bytes to extract from.
    //
    // This also happens to be the fix for the floating launcher button
    // showing up on these tabs: we detect this case first, thing, and return
    // before ever creating the panel or launcher.
    // ============================================================
    function isRawFileViewerPage() {
        const path = (window.location.pathname || '').toLowerCase();
        if (/\.(pdf|docx|xlsx)$/.test(path)) return true;
        try {
            const type = (document.contentType || '').toLowerCase();
            if (type.includes('pdf') || type.includes('wordprocessingml') || type.includes('spreadsheetml')) return true;
        } catch (error) {
            // ignore
        }
        return false;
    }
    function captureCurrentRawFilePage() {
        if (!isIndexingEnabled()) return;
        const url = window.location.href;
        const contentType = (function () {
            try { return document.contentType || ''; } catch (error) { return ''; }
        })();
        const kind = guessFileKind(url, contentType);
        if (!kind) return;
        try {
            GM_xmlhttpRequest({
                method: 'GET',
                url: url,
                responseType: 'arraybuffer',
                onload: function (response) {
                    try {
                        handleCapturedBinary(url, contentType, response.response);
                    } catch (error) {
                        console.warn('SDx Searcher: Could not process raw file page for indexing.', error);
                    }
                },
                onerror: function (error) {
                    console.warn('SDx Searcher: GM_xmlhttpRequest failed for content index capture.', error);
                }
            });
        } catch (error) {
            console.warn('SDx Searcher: Could not start content index capture on this page.', error);
        }
    }
    async function extractTextByKind(kind, arrayBuffer) {
        switch (kind) {
            case 'pdf': return extractTextFromPdf(arrayBuffer);
            case 'docx': return extractTextFromDocx(arrayBuffer);
            case 'xlsx': return extractTextFromXlsx(arrayBuffer);
            default: return '';
        }
    }
    // ============================================================
    // Direct API search: captured auth token
    //
    // Confirmed via DevTools (Headers tab on a real, successful SDx search
    // request) that the native app authenticates its own OData search calls
    // with a plain `Authorization: Bearer <jwt>` header, plus a
    // `Spfconfiguid: <projectKey>` header for project scoping. Sniffing that
    // header off outgoing requests - the same technique the sibling
    // "Previous Version Finder" script already uses successfully - lets us
    // call that same endpoint directly, from whatever tab is already open,
    // instead of opening new tabs and editing the URL hash.
    // ============================================================
    let capturedAuthToken = '';
    function base64UrlDecode(input) {
        try {
            let str = String(input || '').replace(/-/g, '+').replace(/_/g, '/');
            while (str.length % 4) str += '=';
            const decoded = atob(str);
            return decodeURIComponent(
                decoded.split('').map(c => '%' + c.charCodeAt(0).toString(16).padStart(2, '0')).join('')
            );
        } catch (error) {
            return '';
        }
    }
    function decodeJwtPayload(bearerOrToken) {
        try {
            const token = String(bearerOrToken || '').replace(/^Bearer\s+/i, '').trim();
            const parts = token.split('.');
            if (parts.length !== 3) return null;
            const json = base64UrlDecode(parts[1]);
            if (!json) return null;
            return JSON.parse(json);
        } catch (error) {
            return null;
        }
    }
    function getTokenExpiryMs(bearerOrToken) {
        const payload = decodeJwtPayload(bearerOrToken);
        if (!payload || !payload.exp) return null;
        return payload.exp * 1000;
    }
    function isTokenExpired(bearerOrToken, skewMs) {
        const expMs = getTokenExpiryMs(bearerOrToken);
        if (expMs === null) return false; // unknown expiry - don't block on it
        return Date.now() > (expMs - (skewMs || 0));
    }
    function rememberAuthToken(value) {
        if (!value) return;
        const text = String(value).trim();
        if (!/^Bearer\s+eyJ/i.test(text)) return;
        if (capturedAuthToken === text) return;
        capturedAuthToken = text;
        GM_setValue('sdxCapturedAuthToken', text);
    }
    function getAuthToken() {
        if (capturedAuthToken && !isTokenExpired(capturedAuthToken, 30000)) return capturedAuthToken;
        const stored = GM_getValue('sdxCapturedAuthToken', '');
        if (stored && !isTokenExpired(stored, 30000)) {
            capturedAuthToken = stored;
            return stored;
        }
        // Fall back to the sibling scripts' shared key as a bonus source -
        // they use the exact same capture technique, so a token they've
        // already captured is just as valid as one we captured ourselves.
        try {
            const shared = localStorage.getItem('sdx-shared-auth-token') || '';
            if (shared && !isTokenExpired(shared, 30000)) {
                rememberAuthToken(shared);
                return shared;
            }
        } catch (error) {
            // non-fatal
        }
        return stored || capturedAuthToken || '';
    }
    function invalidateAuthToken() {
        capturedAuthToken = '';
        GM_setValue('sdxCapturedAuthToken', '');
    }
    // ============================================================
    // Content index: capture hook
    //
    // Patches fetch and XMLHttpRequest so that when SDx's own app code
    // requests a document that looks like a PDF/DOCX/XLSX (by URL extension
    // or response Content-Type), we read a copy of the response bytes and
    // run extraction on it - without altering what the app itself receives.
    //
    // NOTE (unverified against the live app): this app renders with Angular
    // (`_ngcontent-...` attributes in the side-bar markup), and Angular's
    // HttpClient normally issues requests via XMLHttpRequest rather than
    // fetch, so the XHR hook is the one most likely to actually see document
    // downloads here. Both are installed for coverage. If SDx instead opens
    // documents via a plain link/new tab to a signed URL rather than an
    // in-page XHR/fetch call, neither hook will see those bytes, and capture
    // would need a different approach (e.g. reading from the document
    // viewer's own DOM) - worth confirming once this is tried live.
    // ============================================================
    function isIndexingEnabled() {
        return !!GM_getValue('sdxIndexEnabled', true);
    }
    function shouldCaptureResponse(url, contentType) {
        if (!isIndexingEnabled()) return false;
        return !!guessFileKind(url, contentType);
    }
    function deriveDocId(url) {
        try {
            const parsed = new URL(url, window.location.origin);
            return parsed.pathname + (parsed.search || '');
        } catch (error) {
            return String(url);
        }
    }
    function deriveDocName(url) {
        try {
            const parsed = new URL(url, window.location.origin);
            const segments = parsed.pathname.split('/').filter(Boolean);
            return decodeURIComponent(segments[segments.length - 1] || parsed.pathname);
        } catch (error) {
            return String(url);
        }
    }
    async function storeIndexedDocument(url, kind, text, sourceByteLength) {
        const id = deriveDocId(url);
        // Best-effort project tag for display only - on a raw file-viewer
        // tab there's no SDx route hash to read a project key from, so this
        // falls back to whatever project was last active in the main SPA
        // tab. Search itself is not scoped by project (see runIndexTextSearch).
        const projectKey = getCurrentProjectKey() || GM_getValue('sdxLastActiveProjectKey', '') || '';
        const record = {
            id,
            projectKey,
            name: deriveDocName(url),
            kind,
            text,
            sourceUrl: url,
            sourceByteLength,
            lastAccessedAt: Date.now()
        };
        await idbPutDocument(record);
        const limit = Number(GM_getValue('sdxIndexDocLimit', DEFAULT_INDEX_DOC_LIMIT)) || DEFAULT_INDEX_DOC_LIMIT;
        await enforceIndexDocLimit(limit);
        refreshIndexTabStatsIfOpen();
    }
    function handleCapturedBinary(url, contentType, arrayBuffer) {
        const kind = guessFileKind(url, contentType);
        if (!kind || !arrayBuffer || arrayBuffer.byteLength === 0) return;
        extractTextByKind(kind, arrayBuffer).then(text => {
            if (!text) return;
            storeIndexedDocument(url, kind, text, arrayBuffer.byteLength);
        }).catch(error => {
            console.warn('SDx Searcher: Extraction/storage failed for ' + url, error);
        });
    }
    function patchXhrForCapture() {
        const OriginalOpen = XMLHttpRequest.prototype.open;
        XMLHttpRequest.prototype.open = function (method, url) {
            this.__sdxUrl = url;
            return OriginalOpen.apply(this, arguments);
        };
        // Separate, one-time patch of setRequestHeader so we see the
        // Authorization header SDx's own app sets on its real API calls -
        // confirmed via DevTools to be a Bearer JWT, which the direct
        // search feature below reuses instead of going through Angular's
        // own routing at all.
        if (!XMLHttpRequest.prototype.__sdxAuthHeaderWrapped) {
            const OriginalSetRequestHeader = XMLHttpRequest.prototype.setRequestHeader;
            XMLHttpRequest.prototype.setRequestHeader = function (name, value) {
                try {
                    if (String(name).toLowerCase() === 'authorization') {
                        rememberAuthToken(value);
                    }
                } catch (error) {
                    // non-fatal
                }
                return OriginalSetRequestHeader.apply(this, arguments);
            };
            XMLHttpRequest.prototype.__sdxAuthHeaderWrapped = true;
        }
        const OriginalSend = XMLHttpRequest.prototype.send;
        XMLHttpRequest.prototype.send = function () {
            this.addEventListener('load', function () {
                try {
                    const url = this.__sdxUrl || '';
                    const contentType = this.getResponseHeader ? (this.getResponseHeader('Content-Type') || '') : '';
                    if (!shouldCaptureResponse(url, contentType)) return;
                    if (this.responseType === 'arraybuffer' && this.response) {
                        handleCapturedBinary(url, contentType, this.response);
                    } else if (this.responseType === 'blob' && this.response) {
                        this.response.arrayBuffer().then(buffer => handleCapturedBinary(url, contentType, buffer));
                    }
                } catch (error) {
                    console.warn('SDx Searcher: Could not inspect XHR response for indexing.', error);
                }
            });
            return OriginalSend.apply(this, arguments);
        };
    }
    function patchFetchForCapture() {
        if (typeof window.fetch !== 'function') return;
        const originalFetch = window.fetch;
        window.fetch = function (...args) {
            try {
                const initHeaders = args[1] && args[1].headers;
                if (initHeaders instanceof Headers) {
                    rememberAuthToken(initHeaders.get('authorization') || initHeaders.get('Authorization'));
                } else if (initHeaders && typeof initHeaders === 'object') {
                    rememberAuthToken(initHeaders.authorization || initHeaders.Authorization);
                }
                if (args[0] instanceof Request && args[0].headers) {
                    rememberAuthToken(args[0].headers.get('authorization'));
                }
            } catch (error) {
                // non-fatal
            }
            return originalFetch.apply(this, args).then(response => {
                try {
                    const url = String((args[0] && args[0].url) || args[0] || '');
                    const contentType = (response.headers && response.headers.get) ? (response.headers.get('Content-Type') || '') : '';
                    if (shouldCaptureResponse(url, contentType)) {
                        response.clone().arrayBuffer()
                            .then(buffer => handleCapturedBinary(url, contentType, buffer))
                            .catch(() => {});
                    }
                } catch (error) {
                    console.warn('SDx Searcher: Could not inspect fetch response for indexing.', error);
                }
                return response;
            });
        };
    }
    function initContentIndexCapture() {
        try {
            patchXhrForCapture();
            patchFetchForCapture();
        } catch (error) {
            console.warn('SDx Searcher: Could not install content-index capture hooks.', error);
        }
    }
    // ============================================================
    // Content index: panel UI wiring
    // ============================================================
    async function refreshIndexTab() {
        document.getElementById('sdx-index-enabled-toggle').checked = isIndexingEnabled();
        document.getElementById('sdx-index-doc-limit').value =
            Number(GM_getValue('sdxIndexDocLimit', DEFAULT_INDEX_DOC_LIMIT)) || DEFAULT_INDEX_DOC_LIMIT;
        try {
            cachedIndexDocuments = await idbGetAllDocuments();
        } catch (error) {
            console.warn('SDx Searcher: Could not read content index.', error);
            cachedIndexDocuments = [];
        }
        renderIndexStats(cachedIndexDocuments);
        updatePurgeEstimateDisplay();
        const resultsEl = document.getElementById('sdx-index-search-results');
        if (resultsEl) resultsEl.innerHTML = '';
    }
    // ============================================================
    // Content index: search the cached text itself
    //
    // This is deliberately separate from "Cast Search" on the Searcher tab.
    // Cast Search builds a queryFilter that SDx's own server evaluates
    // against document metadata; it has no way to see inside our local text
    // cache. This searches the cache directly (case-insensitive, all typed
    // words must appear somewhere in the document's extracted text) and
    // links each hit straight back to the exact URL it was captured from -
    // which, since that URL *is* the document's own SDx viewer link, opens
    // the real file with no detour through a list search at all.
    // ============================================================
    function buildSnippet(text, terms, contextChars) {
        const lowerText = text.toLowerCase();
        let matchIndex = -1;
        for (const term of terms) {
            const idx = lowerText.indexOf(term);
            if (idx !== -1 && (matchIndex === -1 || idx < matchIndex)) matchIndex = idx;
        }
        if (matchIndex === -1) return text.slice(0, contextChars * 2).trim();
        const start = Math.max(0, matchIndex - contextChars);
        const end = Math.min(text.length, matchIndex + contextChars);
        let snippet = text.slice(start, end).trim();
        if (start > 0) snippet = '…' + snippet;
        if (end < text.length) snippet = snippet + '…';
        return snippet;
    }
    function searchIndexedDocuments(documents, query) {
        const terms = query.toLowerCase().split(/\s+/).map(t => t.trim()).filter(Boolean);
        if (terms.length === 0) return [];
        return documents.filter(doc => {
            const lowerText = (doc.text || '').toLowerCase();
            return terms.every(term => lowerText.includes(term));
        }).map(doc => ({ doc, snippet: buildSnippet(doc.text || '', terms, 80) }));
    }
    // Shared by both the Content Index tab's own results list and the
    // overlay shown on top of SDx's results page. Documents captured before
    // sourceUrl was added (or in some future edge case where it's missing)
    // render as plain, non-clickable text with a note instead of a link
    // that would silently point at the current page.
    function buildIndexResultsHtml(matches) {
        return matches.map(({ doc, snippet }) => `
            <div style="padding:7px 8px; border-bottom:1px solid #eee; font-size:12px;">
                ${doc.sourceUrl
                    ? `<a href="${escapeHtml(doc.sourceUrl)}"
                          target="_blank"
                          rel="noopener"
                          data-doc-id="${escapeHtml(doc.id)}"
                          class="sdx-index-result-link"
                          style="font-weight:600; color:#0078d4; text-decoration:none; word-break:break-word;">
                          ${escapeHtml(doc.name || doc.id)}
                       </a>`
                    : `<span style="font-weight:600; color:#888; word-break:break-word;">
                          ${escapeHtml(doc.name || doc.id)} <i>(reopen this file once to refresh its link)</i>
                       </span>`
                }
                ${doc.projectKey ? `<span style="color:#888;"> &middot; ${escapeHtml(doc.projectKey)}</span>` : ''}
                <div style="color:#555; margin-top:3px; line-height:1.35;">${escapeHtml(snippet)}</div>
            </div>
        `).join('');
    }
    function wireIndexResultLinks(container) {
        container.querySelectorAll('.sdx-index-result-link').forEach(link => {
            link.addEventListener('click', function () {
                bumpDocumentLastAccessed(this.getAttribute('data-doc-id'));
            });
        });
    }
    function renderIndexSearchResults(matches, query) {
        const resultsEl = document.getElementById('sdx-index-search-results');
        if (!resultsEl) return;
        if (!query) {
            resultsEl.innerHTML = '';
            return;
        }
        if (matches.length === 0) {
            resultsEl.innerHTML = '<div style="padding:8px; font-size:12px; color:#666;">No indexed documents contain all of those words.</div>';
            return;
        }
        resultsEl.innerHTML = buildIndexResultsHtml(matches);
        wireIndexResultLinks(resultsEl);
    }
    async function bumpDocumentLastAccessed(id) {
        try {
            const documents = await idbGetAllDocuments();
            const record = documents.find(d => d.id === id);
            if (!record) return;
            record.lastAccessedAt = Date.now();
            await idbPutDocument(record);
        } catch (error) {
            // Non-critical - just means this hit won't look "recently used" for purge ordering.
        }
    }
    async function runIndexTextSearch() {
        const input = document.getElementById('sdx-index-search-text');
        const query = input ? input.value.trim() : '';
        if (!cachedIndexDocuments) {
            cachedIndexDocuments = await idbGetAllDocuments();
        }
        const matches = searchIndexedDocuments(cachedIndexDocuments, query);
        renderIndexSearchResults(matches, query);
    }
    function renderIndexStats(documents) {
        const stats = computeIndexStats(documents);
        const countEl = document.getElementById('sdx-index-doc-count');
        const sizeEl = document.getElementById('sdx-index-storage-used');
        if (countEl) countEl.textContent = String(stats.count);
        if (sizeEl) sizeEl.textContent = formatBytes(stats.totalBytes);
    }
    function updatePurgeEstimateDisplay() {
        const input = document.getElementById('sdx-index-purge-count');
        const estimateEl = document.getElementById('sdx-index-purge-estimate');
        if (!input || !estimateEl) return;
        const requested = Math.max(0, parseInt(input.value, 10) || 0);
        const oldest = getOldestDocuments(cachedIndexDocuments || [], requested);
        const stats = computeIndexStats(oldest);
        estimateEl.textContent = 'Estimated space freed: ' + formatBytes(stats.totalBytes) +
            ' (' + oldest.length + ' document' + (oldest.length === 1 ? '' : 's') + ')';
    }
    async function saveIndexLimitFromPanel() {
        const input = document.getElementById('sdx-index-doc-limit');
        const limit = Math.max(1, parseInt(input.value, 10) || DEFAULT_INDEX_DOC_LIMIT);
        input.value = limit;
        GM_setValue('sdxIndexDocLimit', limit);
        await enforceIndexDocLimit(limit);
        cachedIndexDocuments = await idbGetAllDocuments();
        renderIndexStats(cachedIndexDocuments);
        updatePurgeEstimateDisplay();
    }
    async function runPurgeOldestFromPanel() {
        const input = document.getElementById('sdx-index-purge-count');
        const requested = Math.max(0, parseInt(input.value, 10) || 0);
        if (requested <= 0) return;
        // Always re-read fresh here rather than trusting cachedIndexDocuments
        // - it can otherwise be a stale snapshot from whenever the tab was
        // last opened, if documents got captured elsewhere since then.
        cachedIndexDocuments = await idbGetAllDocuments();
        const toRemove = getOldestDocuments(cachedIndexDocuments, requested);
        if (toRemove.length === 0) return;
        const confirmed = confirm(
            'Purge ' + toRemove.length + ' oldest indexed document(s), freeing about ' +
            formatBytes(computeIndexStats(toRemove).totalBytes) + '?'
        );
        if (!confirmed) return;
        await idbDeleteDocuments(toRemove.map(d => d.id));
        cachedIndexDocuments = await idbGetAllDocuments();
        renderIndexStats(cachedIndexDocuments);
        input.value = 0;
        updatePurgeEstimateDisplay();
    }
    // Deliberately separate from runPurgeOldestFromPanel and gated behind a
    // SECOND confirmation dialog (not just one) - this deletes everything,
    // not just the oldest N, so it's much easier to fat-finger and much
    // harder to undo.
    async function runPurgeAllFromPanel() {
        // Always re-read fresh - this claims to delete literally everything,
        // so it must not rely on a possibly-stale in-memory snapshot that
        // could be missing documents captured since the tab was last opened.
        cachedIndexDocuments = await idbGetAllDocuments();
        if (cachedIndexDocuments.length === 0) {
            alert('Content index is already empty.');
            return;
        }
        const stats = computeIndexStats(cachedIndexDocuments);
        const firstConfirmed = confirm(
            'This will permanently delete ALL ' + cachedIndexDocuments.length + ' indexed document(s), ' +
            'freeing about ' + formatBytes(stats.totalBytes) + '. This cannot be undone.\n\nContinue?'
        );
        if (!firstConfirmed) return;
        const secondConfirmed = confirm(
            'Are you absolutely sure? This will erase the entire local content index right now.'
        );
        if (!secondConfirmed) return;
        await idbDeleteDocuments(cachedIndexDocuments.map(d => d.id));
        cachedIndexDocuments = await idbGetAllDocuments();
        renderIndexStats(cachedIndexDocuments);
        const purgeCountInput = document.getElementById('sdx-index-purge-count');
        if (purgeCountInput) purgeCountInput.value = 0;
        updatePurgeEstimateDisplay();
        alert('Content index cleared.');
    }
    function toggleIndexEnabledFromPanel() {
        const checked = document.getElementById('sdx-index-enabled-toggle').checked;
        GM_setValue('sdxIndexEnabled', checked);
    }
    function refreshIndexTabStatsIfOpen() {
        if (currentTabId !== 'index') return;
        idbGetAllDocuments().then(documents => {
            cachedIndexDocuments = documents;
            renderIndexStats(documents);
            updatePurgeEstimateDisplay();
        }).catch(() => {});
    }
    // ============================================================
    // Escaping
    // ============================================================
    function escapeHtml(value) {
        return String(value)
            .replaceAll('&', '&amp;')
            .replaceAll('<', '&lt;')
            .replaceAll('>', '&gt;')
            .replaceAll('"', '&quot;')
            .replaceAll("'", '&#039;');
    }
})();
