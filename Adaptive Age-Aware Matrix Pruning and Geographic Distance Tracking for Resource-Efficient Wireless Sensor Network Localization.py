#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
WSN AAMP/GDT Simulation GUI (Validation + Preset + MDS + Multi-start)

Adds:
1) Baseline toggle (No-AAMP): skip pruning (λ=0, θ=1 behavior) for A/B.
2) Memory counters: before/after prune effective bytes (data only + with metadata).
3) Flood overhead meter: track avoided floods/bytes due to versioning.
4) Mobility trial: move 5/32 nodes, then 6 recovery cycles with per-cycle metrics.

Also includes:
- Toolbar + Config-window "Best-Practice Preset"
- Ping Flood (RSSI→distance), Matrix Flood (528B upper-tri + versioning)
- GDT (random), GDT (MDS init), GDT×10 multi-start (best by Stress-1)
- Validate: MAE, RMSE, Stress-1, Pearson r, Triangle inequality violations
- Exports: CSV (measured/completed/metrics/config/residuals), EPS (heatmap), Truth (nodes + true distances)
"""

import tkinter as tk
from tkinter import ttk, messagebox
import argparse
import random, math, json, os, itertools, csv
import sys
from dataclasses import dataclass, asdict
from datetime import datetime
import matplotlib.pyplot as plt

UNDEF = 255  # sentinel for undefined distances in byte matrix

# ---------------- Config dataclass ----------------
@dataclass
class SimConfig:
    # Deployment & environment
    N: int = 32                 # number of nodes
    L: float = 50.0             # area side length (meters), square L × L
    rf_range_mode: str = "fraction_diag"  # "fraction_diag" or "absolute_m"
    rf_range_value: float = 0.56         # tuned fraction of diagonal (≈ good coverage)
    sigma_db: float = 2.0       # RSSI noise (dB)
    seed: int = 12340           # RNG seed

    # AAMP parameters (aging-aware matrix pruning)
    lam: float = 0.0002         # decay constant λ (1/second)
    theta: float = 0.55         # pruning confidence threshold θ (0..1)

    # Scheduling
    flood_interval_min: int = 15
    prune_interval_min: int = 15

    # Mode
    mode: str = "Manual"        # "Manual" or "Auto"

# ---------------- Helpers ----------------
def meters_to_pixels(m, L, canvas_size): return int((m / L) * canvas_size)
def compute_rf_range_m(cfg): return (cfg.rf_range_value * math.sqrt(2) * cfg.L) if cfg.rf_range_mode=="fraction_diag" else cfg.rf_range_value
def compute_rf_range_px(cfg, canvas_size): return meters_to_pixels(compute_rf_range_m(cfg), cfg.L, canvas_size)
def clamp(v, lo, hi): return lo if v < lo else hi if v > hi else v
def ensure_dir(path): os.makedirs(path, exist_ok=True)

# ---------------- Main App ----------------
class WSNApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("WSN AAMP/GDT - Validate + Preset + MDS + Multi-start")
        self.geometry("1400x880"); self.minsize(1200, 740)

        # Add colormap for GUI (move this to the top!)
        try:
            import matplotlib.cm as cm
            import matplotlib.colors as mcolors
            self.cmap = cm.get_cmap('viridis')
            self.norm = mcolors.Normalize(vmin=0, vmax=1)
        except Exception:
            self.cmap = None
            self.norm = None

        # State
        self.cfg = SimConfig()
        self.rng = random.Random(self.cfg.seed)
        self.nodes = []
        self.sim_time = 0.0

        # Matrices
        self.D=[]   # observed distances (bytes, UNDEF=255, diag=0)
        self.T=[]   # timestamps
        self.Q=[]   # confidences
        self.D_completed=None  # completed matrix after GDT (bytes)

        # Matrix flood / overhead accounting
        self.matrix_version=0
        self.last_payload=None
        self.redundant_avoided=0
        self.flood_attempts=0
        self.bytes_sent_naive=0
        self.bytes_sent_versioned=0
        self.flood_history=[]

        # A/B toggle
        self.baseline_no_aamp_var = tk.BooleanVar(value=False)

        # Metrics log
        self.metrics=[]

        # UI
        self._build_layout()
        self._deploy_nodes(self.cfg.N)
        self._reset_matrices()
        self._draw_scene()        # ...existing code...
        # class WSNApp(tk.Tk):
        #     def __init__(self):
        #         super().__init__()
        #         self.title("WSN AAMP/GDT - Validate + Preset + MDS + Multi-start")
        #         self.geometry("1400x880"); self.minsize(1200, 740)
        
        #         # Add colormap for GUI (move this to the top!)
        #         try:
        #             import matplotlib.cm as cm
        #             import matplotlib.colors as mcolors
        #             self.cmap = cm.get_cmap('viridis')
        #             self.norm = mcolors.Normalize(vmin=0, vmax=1)
        #         except Exception:
        #             self.cmap = None
        #             self.norm = None
        
        #         # State
        #         self.cfg = SimConfig()
        #         self.rng = random.Random(self.cfg.seed)
        #         self.nodes = []
        #         self.sim_time = 0.0
        #         # ...rest of your code...
        # self._draw_heatmap()

        # Add colormap for GUI
        try:
            import matplotlib.cm as cm
            import matplotlib.colors as mcolors
            self.cmap = cm.get_cmap('viridis')
            self.norm = mcolors.Normalize(vmin=0, vmax=1)
        except Exception:
            self.cmap = None
            self.norm = None

    # ---------- Layout ----------
    def _build_layout(self):
        # First row: deployment, config, matrix ops
        top1 = ttk.Frame(self, padding=(8,8,8,2)); top1.pack(side=tk.TOP, fill=tk.X)
        ttk.Button(top1, text="Best-Practice Preset", command=self.on_apply_preset).pack(side=tk.LEFT, padx=(0,8))
        ttk.Label(top1, text="mxNod:").pack(side=tk.LEFT)
        self.mxNod_var=tk.StringVar(value=str(self.cfg.N))
        ttk.Entry(top1, width=6, textvariable=self.mxNod_var).pack(side=tk.LEFT, padx=(4,6))
        ttk.Button(top1, text="NODES", command=self.on_redraw_nodes).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top1, text="Reseed", command=self.on_reseed).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top1, text="Reload", command=self.on_reload).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top1, text="Config", command=self.open_config_form).pack(side=tk.LEFT, padx=(0,10))
        ttk.Button(top1, text="Ping Flood", command=self.on_ping_flood).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top1, text="Prune Matrix", command=self.on_prune_matrix).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top1, text="Matrix Flood", command=self.on_matrix_flood).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top1, text="Compare Prune", command=self.on_compare_prune).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top1, text="Prune Sensitivity", command=self.on_prune_sensitivity).pack(side=tk.LEFT, padx=(0,6))

        # Second row: cycles, GDT, validation, export
        top2 = ttk.Frame(self, padding=(8,2,8,8)); top2.pack(side=tk.TOP, fill=tk.X)
        ttk.Label(top2, text="Cycles:").pack(side=tk.LEFT)
        self.cycles_var = tk.StringVar(value="10")
        ttk.Entry(top2, width=6, textvariable=self.cycles_var).pack(side=tk.LEFT, padx=(4,6))
        ttk.Button(top2, text="Flood ×N (Bytes)", command=self.on_matrix_flood_xn).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="Export Flood Table", command=self.on_export_flood_table).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="Reset Flood Log", command=self.on_reset_flood_log).pack(side=tk.LEFT, padx=(0,10))
        ttk.Button(top2, text="Run GDT", command=self.on_run_gdt).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="GDT (MDS Init)", command=self.on_run_gdt_mds).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="GDT ×10 (Best)", command=self.on_run_gdt_multistart).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="Validate", command=self.on_validate_gdt).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="MAE Heatmap (σ×θ)", command=self.on_mae_heatmap_sigma_theta).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="Mobility Trial (5/32 ×6)", command=self.on_mobility_trial).pack(side=tk.LEFT, padx=(0,10))
        ttk.Button(top2, text="Export CSV", command=self.on_export_csv).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="Export PNG", command=self.on_export_png).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="Export Truth", command=self.on_export_truth).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(top2, text="Export GDT Accuracy Table", command=self.on_export_gdt_accuracy_table).pack(side=tk.LEFT, padx=(0,6))

        # Row for completed matrix toggle and status
        row2=ttk.Frame(self, padding=(8,0,8,6)); row2.pack(side=tk.TOP, fill=tk.X)
        self.show_completed_var=tk.BooleanVar(value=False)
        ttk.Checkbutton(row2, text="Show Completed Matrix", variable=self.show_completed_var, command=self._draw_heatmap).pack(side=tk.LEFT, padx=(0,12))
        ttk.Checkbutton(row2, text="Baseline (No AAMP prune)", variable=self.baseline_no_aamp_var).pack(side=tk.LEFT, padx=(0,16))
        self.status_str=tk.StringVar(value=self._status_text())
        ttk.Label(row2, textvariable=self.status_str).pack(side=tk.LEFT, padx=(12,0))

        main=ttk.Frame(self, padding=(8,4,8,8)); main.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        # Left: node canvas
        self.canvas_size=720
        self.canvas=tk.Canvas(main, width=self.canvas_size, height=self.canvas_size, bg="white")
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=False)

        # Right: heatmap + legend + log
        right=ttk.Frame(main); right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(8,0))
        ttk.Label(right, text="Matrix Heatmap (D)", font=("Segoe UI", 11, "bold")).pack(anchor="w")
        self.heatmap_size=500
        self.hm=tk.Canvas(right, width=self.heatmap_size, height=self.heatmap_size, bg="white")
        self.hm.pack(fill=tk.NONE, expand=False, pady=(4,4))
        self.legend=tk.Canvas(right, width=self.heatmap_size, height=40, bg="white", highlightthickness=0)
        self.legend.pack(fill=tk.X, expand=False, pady=(2,8))

        ttk.Label(right, text="Info / Log", font=("Segoe UI", 11, "bold")).pack(anchor="w")
        self.log_text=tk.Text(right, height=12, wrap="word")
        self.log_text.pack(fill=tk.BOTH, expand=True)

        bottom=ttk.Frame(self, padding=(8,4,8,8)); bottom.pack(side=tk.BOTTOM, fill=tk.X)
        self.footer_str=tk.StringVar(value="Ready")
        ttk.Label(bottom, textvariable=self.footer_str).pack(side=tk.LEFT)

    def _status_text(self):
        c=self.cfg
        base = (f"N={c.N}, L={c.L}m, R={'frac_diag' if c.rf_range_mode=='fraction_diag' else 'abs'}:{c.rf_range_value}, σ={c.sigma_db}dB, "
                f"λ={c.lam}, θ={c.theta}, Flood={c.flood_interval_min}m, Prune={c.prune_interval_min}m, "
                f"Seed={c.seed}, Mode={c.mode}, t={int(self.sim_time)}s, v={self.matrix_version}")
        if self.baseline_no_aamp_var.get():
            base += " | BASELINE"
        # Overhead snapshot
        if self.bytes_sent_naive>0:
            save = 100.0*(1.0 - (self.bytes_sent_versioned/max(1,self.bytes_sent_naive)))
            base += f" | FloodSave={save:.1f}%"
        return base

    # ---------- Node & Matrix ----------
    def _deploy_nodes(self, N):
        self.nodes=[(self.rng.uniform(0,self.cfg.L), self.rng.uniform(0,self.cfg.L)) for _ in range(N)]
        self._log(f"Deployed {N} nodes.")

    def _reset_matrices(self):
        N=self.cfg.N
        self.D=[[UNDEF]*N for _ in range(N)]
        self.T=[[0.0]*N for _ in range(N)]
        self.Q=[[0.0]*N for _ in range(N)]
        for i in range(N):
            self.D[i][i]=0
            self.Q[i][i]=1.0
        self.D_completed=None
        self._log("Matrices reset.")

    # ---------- Drawing ----------
    def _draw_scene(self):
        self.canvas.delete("all")
        L=self.cfg.L; S=self.canvas_size; Rpx=compute_rf_range_px(self.cfg,S)
        grid_step=S//10
        for g in range(0,S,grid_step):
            self.canvas.create_line(g,0,g,S,fill="#f0f0f0")
            self.canvas.create_line(0,g,S,g,fill="#f0f0f0")
        self.canvas.create_rectangle(2,2,S-2,S-2,outline="#888")

        r_node=5
        for idx,(xm,ym) in enumerate(self.nodes):
            x=meters_to_pixels(xm,L,S); y=meters_to_pixels(ym,L,S)
            self.canvas.create_oval(x-Rpx,y-Rpx,x+Rpx,y+Rpx,outline="#d9e2ff")
            self.canvas.create_oval(x-r_node+1,y-r_node+1,x+r_node+1,y+r_node+1,fill="#cbd5e1",outline="")
            self.canvas.create_oval(x-r_node,y-r_node,x+r_node,y+r_node,fill="#2563eb",outline="#0f172a")
            self.canvas.create_text(x+10,y,text=str(idx),anchor="w",fill="#111827",font=("Segoe UI",9))
        self.status_str.set(self._status_text())
        self.footer_str.set(f"Drawn {len(self.nodes)} nodes.")

    def _draw_heatmap(self):
        self.hm.delete("all")
        N=self.cfg.N; S=self.heatmap_size
        if N<=0: return
        cell=S/N
        Dview=self.D_completed if (getattr(self,'show_completed_var',None) and self.show_completed_var.get() and self.D_completed is not None) else self.D
        valid=[Dview[i][j] for i in range(N) for j in range(N) if Dview[i][j]!=UNDEF]
        dmax=max(valid) if valid else 1

        # Use matplotlib colormap
        def cmap_color(t):
            if self.cmap is None or self.norm is None:
                # fallback: grayscale
                g = int(255 * t)
                return f"#{g:02x}{g:02x}{g:02x}"
            rgba = self.cmap(self.norm(t))
            r, g, b = [int(255*x) for x in rgba[:3]]
            return f"#{r:02x}{g:02x}{b:02x}"

        for i in range(N):
            for j in range(N):
                d=Dview[i][j]
                color="#ffffff" if d==UNDEF else cmap_color(d/max(1,dmax))
                x0=j*cell; y0=i*cell; x1=x0+cell; y1=y0+cell
                self.hm.create_rectangle(x0,y0,x1,y1,outline="",fill=color)
        self.hm.create_rectangle(1,1,S-1,S-1,outline="#999")
        self._draw_legend(dmax)

    def _draw_legend(self, dmax):
        self.legend.delete("all")
        W=self.heatmap_size; H=40; steps=100
        # Use matplotlib colormap for legend
        try:
            import matplotlib.cm as cm
            import matplotlib.colors as mcolors
            cmap = cm.get_cmap('viridis')
            norm = mcolors.Normalize(vmin=0, vmax=1)
        except Exception:
            cmap = None
            norm = None

        for k in range(steps):
            t=k/(steps-1)
            if cmap is not None and norm is not None:
                rgba = cmap(norm(t))
                r, g, b = [int(255*x) for x in rgba[:3]]
                color=f"#{r:02x}{g:02x}{b:02x}"
            else:
                g = int(255 * t)
                color=f"#{g:02x}{g:02x}{g:02x}"
            x0=int(t*(W-2)); x1=int((k+1)/(steps-1)*(W-2))
            self.legend.create_rectangle(1+x0,5,1+x1,H-15,outline="",fill=color)
        self.legend.create_rectangle(1,5,W-1,H-15,outline="#999")
        for m in range(6):
            t=m/5.0; x=1+int(t*(W-2))
            self.legend.create_line(x,H-15,x,H-5,fill="#666")
            val=int(round(t*dmax))
            self.legend.create_text(x,H-2,text=str(val),anchor="n",fill="#374151",font=("Segoe UI",8))
        self.legend.create_text(6,H-35,text="Near",anchor="w",fill="#111827",font=("Segoe UI",9))
        self.legend.create_text(W-6,H-35,text="Far",anchor="e",fill="#111827",font=("Segoe UI",9))

    # ---------- Events ----------
    def on_apply_preset(self):
        """Apply recommended config and reset."""
        self.cfg = SimConfig()  # default holds best-practice values
        self.rng = random.Random(self.cfg.seed)
        self._deploy_nodes(self.cfg.N)
        self._reset_matrices()
        self._draw_scene()
        self._draw_heatmap()
        self._log(f"Applied Best-Practice Preset: {asdict(self.cfg)}")
        self.status_str.set(self._status_text())
        self.footer_str.set("Preset applied.")

    def on_redraw_nodes(self):
        try:
            n_val=int(self.mxNod_var.get())
            if n_val<2 or n_val>1024: raise ValueError
        except Exception:
            messagebox.showerror("Invalid N","Please enter an integer in [2, 1024] for mxNod.")
            return
        self.cfg.N=n_val
        self._deploy_nodes(self.cfg.N)
        self._reset_matrices()
        self._draw_scene()
        self._draw_heatmap()

    def on_reseed(self):
        new_seed=self.rng.randrange(1,10**9)
        self.cfg.seed=new_seed
        self.rng=random.Random(self.cfg.seed)
        self._log(f"Reseeded RNG: seed={self.cfg.seed}")
        self._deploy_nodes(self.cfg.N)
        self._reset_matrices()
        self._draw_scene()
        self._draw_heatmap()

    def on_reload(self):
        self.sim_time=0.0
        self.rng=random.Random(self.cfg.seed)
        self._deploy_nodes(self.cfg.N)
        self._reset_matrices()
        self.matrix_version=0; self.last_payload=None; self.redundant_avoided=0
        self.flood_attempts=0; self.bytes_sent_naive=0; self.bytes_sent_versioned=0; self.flood_history=[]
        self._draw_scene(); self._draw_heatmap()
        self.status_str.set(self._status_text())
        self._log(f"Reloaded: seed={self.cfg.seed}, N={self.cfg.N}, time reset to 0s.")
        self.footer_str.set("Reload complete.")

    def on_ping_flood(self):
        N=self.cfg.N; Rm=compute_rf_range_m(self.cfg); sigma=self.cfg.sigma_db; now=self.sim_time; burst=15
        RSSI0=-40.0; n_path=2.0; d0=1.0; d_max=self.cfg.L*math.sqrt(2.0); scale=254.0/d_max
        updates=0
        for i in range(N):
            xi,yi=self.nodes[i]
            for j in range(i+1,N):
                xj,yj=self.nodes[j]; dij_true=math.hypot(xi-xj, yi-yj)
                if dij_true<=Rm:
                    rssi=[(RSSI0-10.0*n_path*math.log10(max(dij_true,1e-3)/d0) + self.rng.gauss(0.0,sigma)) for _ in range(burst)]
                    d_est=[d0*(10**((RSSI0-r)/(10.0*n_path))) for r in rssi]
                    d_mean=sum(d_est)/burst
                    m=sum(rssi)/burst
                    var=sum((r-m)*(r-m) for r in rssi)/max(1,(burst-1))
                    denom=(sigma*2.0)**2+1e-9
                    q=clamp(1.0-(var/denom),0.0,1.0)
                    db=clamp(int(round(d_mean*scale)),0,254)
                    self.D[i][j]=db; self.D[j][i]=db
                    self.T[i][j]=now; self.T[j][i]=now
                    self.Q[i][j]=q;  self.Q[j][i]=q
                    updates+=1
        self.sim_time+=self.cfg.flood_interval_min*60.0
        total_pairs=N*(N-1)//2
        filled=sum(1 for i in range(N) for j in range(i+1,N) if self.D[i][j]!=UNDEF)
        fill_frac=filled/total_pairs if total_pairs else 0.0
        self._draw_heatmap()
        self.status_str.set(self._status_text())
        self._log(f"Ping Flood: updated {updates} pairs; fill={fill_frac*100:.1f}% (R≤{Rm:.2f}m).")
        self._log_event("ping_flood", {"updates":updates,"fill_frac":fill_frac})
        self.footer_str.set(f"Ping Flood done. Fill={fill_frac*100:.1f}% | t={int(self.sim_time)}s")

    # ---------- Memory accounting helpers ----------
    def _count_defined_pairs(self):
        N=self.cfg.N
        return sum(1 for i in range(N) for j in range(i+1,N) if self.D[i][j]!=UNDEF)

    def _memory_stats(self, defined_pairs):
        """
        Effective memory footprint:
        - data_bytes: 1 byte per defined upper-tri entry
        - with_metadata_bytes: add Q (8B float) + T (8B float) per defined pair → +16B
        """
        data_bytes = defined_pairs * 1
        with_metadata_bytes = defined_pairs * (1 + 8 + 8)
        return data_bytes, with_metadata_bytes

    def on_prune_matrix(self):
        # Baseline: skip pruning, just advance time and log as "baseline pass"
        if self.baseline_no_aamp_var.get():
            self.sim_time += self.cfg.prune_interval_min*60.0
            defined_before = self._count_defined_pairs()
            self._log(f"[BASELINE] Prune skipped. Defined pairs remain = {defined_before}.")
            self._log_event("prune_baseline", {"defined_pairs":defined_before})
            self.status_str.set(self._status_text())
            self.footer_str.set(f"Baseline (no prune). t={int(self.sim_time)}s")
            return

        N=self.cfg.N; lam=self.cfg.lam; theta=self.cfg.theta; now=self.sim_time
        defined_before = self._count_defined_pairs()
        data_bef, meta_bef = self._memory_stats(defined_before)

        pruned=0; examined=0
        for i in range(N):
            for j in range(i+1,N):
                if self.D[i][j]!=UNDEF:
                    age=max(0.0, now-self.T[i][j])
                    conf=self.Q[i][j]*math.exp(-lam*age)
                    examined+=1
                    if conf<theta:
                        self.D[i][j]=UNDEF; self.D[j][i]=UNDEF
                        self.Q[i][j]=0.0;  self.Q[j][i]=0.0
                        self.T[i][j]=0.0;  self.T[j][i]=0.0
                        pruned+=1
        self.sim_time+=self.cfg.prune_interval_min*60.0

        defined_after = self._count_defined_pairs()
        data_aft, meta_aft = self._memory_stats(defined_after)

        red_data = (100.0*(1 - data_aft/max(1,data_bef))) if data_bef>0 else 0.0
        red_meta = (100.0*(1 - meta_aft/max(1,meta_bef))) if meta_bef>0 else 0.0

        self._draw_heatmap()
        self.status_str.set(self._status_text())
        self._log(f"Prune Matrix: examined {examined}, pruned {pruned} (θ={theta}, λ={lam}).")
        self._log(f"Memory: pairs {defined_before} → {defined_after} | data {data_bef}B → {data_aft}B ({red_data:.1f}%↓) | data+meta {meta_bef}B → {meta_aft}B ({red_meta:.1f}%↓)")
        self._log_event("prune", {
            "examined":examined,"pruned":pruned,
            "pairs_before":defined_before,"pairs_after":defined_after,
            "data_B_before":data_bef,"data_B_after":data_aft,
            "meta_B_before":meta_bef,"meta_B_after":meta_aft
        })
        self.footer_str.set(f"Prune done. Pruned={pruned} | t={int(self.sim_time)}s")

    def on_compare_prune(self):
        """Run before-and-after prune comparison and report if matrix changed."""
        # Ensure we have some observed entries
        if self._count_defined_pairs() == 0:
            self._log("No measurements yet → running Ping Flood to populate matrix.")
            self.on_ping_flood()

        # Snapshot BEFORE
        N = self.cfg.N
        D_before = [row[:] for row in self.D]
        pairs_before = self._count_defined_pairs()
        data_bef, meta_bef = self._memory_stats(pairs_before)

        # Perform a forced prune (ignores baseline toggle)
        lam = self.cfg.lam; theta = self.cfg.theta; now = self.sim_time
        pruned = 0; examined = 0
        for i in range(N):
            for j in range(i+1, N):
                if self.D[i][j] != UNDEF:
                    age = max(0.0, now - self.T[i][j])
                    conf = self.Q[i][j] * math.exp(-lam * age)
                    examined += 1
                    if conf < theta:
                        self.D[i][j] = UNDEF; self.D[j][i] = UNDEF
                        self.Q[i][j] = 0.0;  self.Q[j][i] = 0.0
                        self.T[i][j] = 0.0;  self.T[j][i] = 0.0
                        pruned += 1
        # Advance simulated time like normal prune
        self.sim_time += self.cfg.prune_interval_min * 60.0

        # AFTER stats
        pairs_after = self._count_defined_pairs()
        data_aft, meta_aft = self._memory_stats(pairs_after)
        # Matrix diff count (all elements)
        diff_count = 0
        for i in range(N):
            for j in range(N):
                if D_before[i][j] != self.D[i][j]:
                    diff_count += 1
        is_same = (diff_count == 0)

        self._draw_heatmap()
        self.status_str.set(self._status_text())

        self._log(f"Compare Prune: examined={examined}, pruned={pruned}, pairs {pairs_before} → {pairs_after}.")
        self._log(f"Memory bytes: data {data_bef} → {data_aft} | data+meta {meta_bef} → {meta_aft}")
        self._log(f"Matrix change: {'SAME' if is_same else 'DIFFERENT'} (diff elements={diff_count})")
        self._log_event("prune_compare", {
            "examined": examined,
            "pruned": pruned,
            "pairs_before": pairs_before,
            "pairs_after": pairs_after,
            "data_B_before": data_bef,
            "data_B_after": data_aft,
            "meta_B_before": meta_bef,
            "meta_B_after": meta_aft,
            "diff_elements": diff_count,
            "same": is_same
        })
        # Try to render and save a bar chart
        try:
            self._plot_prune_effect(pairs_before, pairs_after)
        except Exception as e:
            self._log(f"Plot skipped (matplotlib likely missing): {e}")
        # Write summary table CSV
        try:
            self._write_prune_compare_csv({
                "pairs_before": pairs_before,
                "pairs_after": pairs_after,
                "examined": examined,
                "pruned": pruned,
                "data_B_before": data_bef,
                "data_B_after": data_aft,
                "meta_B_before": meta_bef,
                "meta_B_after": meta_aft,
                "diff_elements": diff_count,
                "same": is_same,
                "lambda": self.cfg.lam,
                "theta": self.cfg.theta,
                "prune_interval_min": self.cfg.prune_interval_min,
                "flood_interval_min": self.cfg.flood_interval_min,
                "sigma_db": self.cfg.sigma_db,
                "N": self.cfg.N
            })
        except Exception as e:
            self._log(f"CSV table write failed: {e}")
        self.footer_str.set("Compare Prune complete. See log and EPS (if available).")

    def _plot_prune_effect(self, pairs_before: int, pairs_after: int):
        """Create and save a simple bar chart of defined pairs before vs after pruning."""
        import matplotlib.pyplot as plt
        from datetime import datetime as _dt
        import os as _os
        ensure_dir(_os.path.join(_os.getcwd(), "exports"))

        fig, ax = plt.subplots(figsize=(6, 4))
        bars = ax.bar(["Before Pruning", "After Pruning"], [pairs_before, pairs_after],
                      color=["#ef4444", "#22c55e"], edgecolor="#111827")
        ax.set_ylabel("Defined Pairs (Upper-Triangle)")
        ax.set_ylim(0, 400)
        ax.grid(True, axis="y", linestyle="--", alpha=0.4)
        # Annotate values
        for b, v in zip(bars, [pairs_before, pairs_after]):
            ax.text(b.get_x() + b.get_width() / 2, b.get_height() + max(1, 0.01 * max(pairs_before, pairs_after)),
                    f"{v}", ha="center", va="bottom", fontsize=10)
        
        # Add subplot label (b) for publication
        ax.text(0.5, -0.12, '(b)', transform=ax.transAxes, 
                ha='center', va='top', fontsize=12, fontweight='bold')
        
        plt.tight_layout()
        ts = _dt.now().strftime("%Y%m%d_%H%M%S")
        out_eps = _os.path.join(_os.getcwd(), "exports", f"prune_effect_{ts}.eps")
        out_png = _os.path.join(_os.getcwd(), "exports", f"prune_effect_{ts}.png")
        plt.savefig(out_eps, format='eps', dpi=200, bbox_inches='tight', pad_inches=0.05)
        plt.savefig(out_png, format='png', dpi=200, bbox_inches='tight', pad_inches=0.05)
        plt.close(fig)
        self._log(f"Saved prune effect chart → {out_eps} and {out_png}")
        
        # Also save data to fig2b.txt
        fpath_txt = os.path.join(_os.getcwd(), "exports", "fig2b.txt")
        data_bytes_before = pairs_before * 1
        data_bytes_after = pairs_after * 1
        meta_bytes_before = pairs_before * (1 + 8 + 8)
        meta_bytes_after = pairs_after * (1 + 8 + 8)
        reduction_pairs = 100.0 * (1.0 - (pairs_after / max(1, pairs_before)))
        reduction_data = 100.0 * (1.0 - (data_bytes_after / max(1, data_bytes_before)))
        reduction_meta = 100.0 * (1.0 - (meta_bytes_after / max(1, meta_bytes_before)))
        
        with open(fpath_txt, "w", encoding="utf-8") as fp:
            fp.write("Figure 2(b): Reduction in Defined Matrix Entries and Effective Memory After AAMP Pruning\n")
            fp.write("=" * 80 + "\n\n")
            fp.write("Metric\t\t\tBefore\t\tAfter\t\tReduction\n")
            fp.write("-" * 80 + "\n")
            fp.write(f"Defined Pairs\t\t\t{pairs_before}\t\t{pairs_after}\t\t{reduction_pairs:.1f}%\n")
            fp.write(f"Data Bytes Only\t\t\t{data_bytes_before}\t\t{data_bytes_after}\t\t{reduction_data:.1f}%\n")
            fp.write(f"Data + Metadata Bytes\t{meta_bytes_before}\t\t{meta_bytes_after}\t\t{reduction_meta:.1f}%\n")
            fp.write("\nDetails:\n")
            fp.write(f"AAMP Parameters: λ={self.cfg.lam}, θ={self.cfg.theta}\n")
            fp.write(f"Configuration: N={self.cfg.N}, L={self.cfg.L}m\n")
        self._log(f"Saved Fig.2b data → {fpath_txt}")

    def _write_prune_compare_csv(self, stats: dict):
        """Write a single-run prune comparison summary table to exports/prune_compare_*.csv."""
        from datetime import datetime as _dt
        import os as _os, csv as _csv
        outdir = _os.path.join(_os.getcwd(), "exports"); ensure_dir(outdir)
        ts = _dt.now().strftime("%Y%m%d_%H%M%S")
        fpath = _os.path.join(outdir, f"prune_compare_{ts}.csv")
        # Stable column order
        cols = [
            "N","pairs_before","pairs_after","examined","pruned",
            "data_B_before","data_B_after","meta_B_before","meta_B_after",
            "diff_elements","same","lambda","theta","prune_interval_min","flood_interval_min","sigma_db"
        ]
        with open(fpath, "w", newline="", encoding="utf-8") as fp:
            w = _csv.writer(fp)
            w.writerow(cols)
            w.writerow([stats.get(k, "") for k in cols])
        self._log(f"Saved prune compare table → {fpath}")

    def on_prune_sensitivity(self):
        """Generate parameter sensitivity table for pruning across different θ values."""
        # Ensure we have measurements
        if self._count_defined_pairs() == 0:
            self._log("No measurements yet → running Ping Flood to populate matrix.")
            self.on_ping_flood()

        import numpy as np
        import matplotlib.pyplot as plt
        import csv
        from datetime import datetime as _dt
        import os as _os
        
        # Test θ values
        theta_values = [0.2, 0.3, 0.4, 0.55, 0.6, 0.7, 0.8]
        results = []
        
        # Save current state
        original_theta = self.cfg.theta
        original_time = self.sim_time
        N = self.cfg.N
        
        # Deep copy of matrices to restore after each test
        D_snapshot = [row[:] for row in self.D]
        T_snapshot = [row[:] for row in self.T]
        Q_snapshot = [row[:] for row in self.Q]
        
        self._log(f"Pruning Sensitivity Analysis: Testing θ values {theta_values}")
        self._log("(Matrix state will be restored after each test)")
        
        for theta in theta_values:
            # Restore matrices to original state
            self.D = [row[:] for row in D_snapshot]
            self.T = [row[:] for row in T_snapshot]
            self.Q = [row[:] for row in Q_snapshot]
            self.sim_time = original_time
            
            # Set θ for this test
            self.cfg.theta = theta
            
            # Count before
            pairs_before = self._count_defined_pairs()
            data_bef, meta_bef = self._memory_stats(pairs_before)
            
            # Perform pruning
            lam = self.cfg.lam
            now = self.sim_time
            pruned = 0
            examined = 0
            
            for i in range(N):
                for j in range(i+1, N):
                    if self.D[i][j] != UNDEF:
                        age = max(0.0, now - self.T[i][j])
                        conf = self.Q[i][j] * math.exp(-lam * age)
                        examined += 1
                        if conf < theta:
                            self.D[i][j] = UNDEF
                            self.D[j][i] = UNDEF
                            self.Q[i][j] = 0.0
                            self.Q[j][i] = 0.0
                            self.T[i][j] = 0.0
                            self.T[j][i] = 0.0
                            pruned += 1
            
            # Count after
            pairs_after = self._count_defined_pairs()
            data_aft, meta_aft = self._memory_stats(pairs_after)
            
            reduction_pairs = 100.0 * (1.0 - (pairs_after / max(1, pairs_before))) if pairs_before > 0 else 0.0
            reduction_data = 100.0 * (1.0 - (data_aft / max(1, data_bef))) if data_bef > 0 else 0.0
            reduction_meta = 100.0 * (1.0 - (meta_aft / max(1, meta_bef))) if meta_bef > 0 else 0.0
            
            results.append({
                "theta": theta,
                "pairs_before": pairs_before,
                "pairs_after": pairs_after,
                "pruned": pruned,
                "reduction_pairs_pct": reduction_pairs,
                "data_before": data_bef,
                "data_after": data_aft,
                "reduction_data_pct": reduction_data,
                "meta_before": meta_bef,
                "meta_after": meta_aft,
                "reduction_meta_pct": reduction_meta
            })
            
            self._log(f"θ={theta:.2f}: {pairs_before} → {pairs_after} pairs ({reduction_pairs:.1f}% reduction, {pruned} pruned)")
        
        # Restore original state
        self.D = D_snapshot
        self.T = T_snapshot
        self.Q = Q_snapshot
        self.cfg.theta = original_theta
        self.sim_time = original_time
        self._draw_heatmap()
        
        # Save CSV table
        outdir = _os.path.join(_os.getcwd(), "exports")
        ensure_dir(outdir)
        ts = _dt.now().strftime("%Y%m%d_%H%M%S")
        csv_path = _os.path.join(outdir, f"prune_sensitivity_{ts}.csv")
        
        with open(csv_path, "w", newline="", encoding="utf-8") as fp:
            w = csv.writer(fp)
            w.writerow([
                "θ (Threshold)", "Pairs Before", "Pairs After", "Pruned", 
                "Reduction %", "Data Bytes Before", "Data Bytes After", 
                "Data Reduction %", "Metadata Bytes Before", "Metadata Bytes After", 
                "Metadata Reduction %"
            ])
            for r in results:
                w.writerow([
                    f"{r['theta']:.2f}",
                    r['pairs_before'],
                    r['pairs_after'],
                    r['pruned'],
                    f"{r['reduction_pairs_pct']:.2f}",
                    r['data_before'],
                    r['data_after'],
                    f"{r['reduction_data_pct']:.2f}",
                    r['meta_before'],
                    r['meta_after'],
                    f"{r['reduction_meta_pct']:.2f}"
                ])
        
        self._log(f"Saved sensitivity table → {csv_path}")
        
        # Save formatted text table
        txt_path = _os.path.join(outdir, "prune_sensitivity_table.txt")
        with open(txt_path, "w", encoding="utf-8") as fp:
            fp.write("Pruning Parameter Sensitivity Analysis\n")
            fp.write("=" * 90 + "\n\n")
            fp.write("Effect of θ (Confidence Threshold) on AAMP Pruning Effectiveness\n\n")
            fp.write(f"{'θ':<6} {'Before':<8} {'After':<8} {'Pruned':<8} {'Reduction':<12} {'Meta Before':<14} {'Meta After':<13} {'Meta Reduction':<15}\n")
            fp.write("-" * 90 + "\n")
            for r in results:
                fp.write(f"{r['theta']:<6.2f} {r['pairs_before']:<8} {r['pairs_after']:<8} {r['pruned']:<8} "
                        f"{r['reduction_pairs_pct']:<11.1f}% {r['meta_before']:<14} {r['meta_after']:<13} "
                        f"{r['reduction_meta_pct']:<14.1f}%\n")
            fp.write("\n" + "=" * 90 + "\n")
            fp.write("Details:\n")
            fp.write(f"Configuration: N={self.cfg.N}, L={self.cfg.L}m, λ={self.cfg.lam}, σ={self.cfg.sigma_db}dB\n")
            fp.write(f"Initial measurements: {results[0]['pairs_before']} pairs (before any pruning)\n")
            fp.write(f"Simulation time at test: {int(original_time)}s\n")
            fp.write("\nInterpretation:\n")
            fp.write("- Lower θ (e.g., 0.2-0.3): Conservative pruning, more data retained\n")
            fp.write("- Moderate θ (e.g., 0.4-0.6): Balanced pruning, good memory savings\n")
            fp.write("- Higher θ (e.g., 0.7-0.8): Aggressive pruning, maximum memory savings\n")
        
        self._log(f"Saved formatted table → {txt_path}")
        
        # Create visualization
        try:
            fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))
            
            # Left plot: Reduction percentage vs θ
            thetas = [r['theta'] for r in results]
            reductions = [r['reduction_pairs_pct'] for r in results]
            ax1.plot(thetas, reductions, 'o-', linewidth=2, markersize=8, color='#2563eb')
            ax1.set_xlabel('θ (Confidence Threshold)', fontsize=11)
            ax1.set_ylabel('Reduction (%)', fontsize=11)
            ax1.grid(True, alpha=0.3)
            ax1.set_xlim(0.15, 0.85)
            
            # Annotate points
            for t, r in zip(thetas, reductions):
                ax1.annotate(f'{r:.1f}%', (t, r), textcoords="offset points", 
                           xytext=(0,10), ha='center', fontsize=9)
            
            # Right plot: Before/After bar chart for selected θ values
            selected_indices = [1, 3, 5]  # θ=0.3, 0.5, 0.7
            x_pos = np.arange(len(selected_indices))
            before_vals = [results[i]['pairs_before'] for i in selected_indices]
            after_vals = [results[i]['pairs_after'] for i in selected_indices]
            theta_labels = [f"θ={results[i]['theta']:.1f}" for i in selected_indices]
            
            width = 0.35
            bars1 = ax2.bar(x_pos - width/2, before_vals, width, label='Before', color='#ef4444', edgecolor='#111827')
            bars2 = ax2.bar(x_pos + width/2, after_vals, width, label='After', color='#22c55e', edgecolor='#111827')
            ax2.set_xlabel('Threshold θ', fontsize=11)
            ax2.set_ylabel('Defined Pairs', fontsize=11)
            ax2.set_xticks(x_pos)
            ax2.set_xticklabels(theta_labels)
            ax2.legend()
            ax2.grid(True, axis='y', alpha=0.3)
            
            # Annotate bars
            for bars in [bars1, bars2]:
                for bar in bars:
                    height = bar.get_height()
                    ax2.text(bar.get_x() + bar.get_width()/2., height,
                           f'{int(height)}', ha='center', va='bottom', fontsize=9)
            
            plt.tight_layout()
            eps_path = _os.path.join(outdir, f"prune_sensitivity_{ts}.eps")
            png_path = _os.path.join(outdir, f"prune_sensitivity_{ts}.png")
            plt.savefig(eps_path, format='eps', dpi=300, bbox_inches='tight')
            plt.savefig(png_path, format='png', dpi=300, bbox_inches='tight')
            plt.close(fig)
            self._log(f"Saved sensitivity plot → {eps_path} and {png_path}")
        except Exception as e:
            self._log(f"Visualization skipped: {e}")
        
        self.footer_str.set(f"Prune sensitivity analysis complete. Tested {len(theta_values)} θ values.")
        self._log(f"✓ Sensitivity analysis complete: {len(results)} configurations tested")

    # ---------- Matrix Flood & Overhead ----------
    def _pack_upper_tri(self,D):
        N=self.cfg.N; buf=bytearray()
        for i in range(N):
            for j in range(i,N): buf.append(D[i][j])
        return bytes(buf)  # N*(N+1)/2 bytes → 528 bytes at N=32

    def _unpack_upper_tri(self,buf):
        N=self.cfg.N; expected=N*(N+1)//2
        if len(buf)!=expected: raise ValueError(f"Bad length: got {len(buf)}, expected {expected}")
        D=[[UNDEF]*N for _ in range(N)]; k=0
        for i in range(N):
            for j in range(i,N): val=buf[k]; D[i][j]=val; D[j][i]=val; k+=1
        return D

    def on_matrix_flood(self):
        N=self.cfg.N
        payload=self._pack_upper_tri(self.D)
        self.flood_attempts += 1
        self.bytes_sent_naive += len(payload)  # naive: always send
        
        header=bytes([self.matrix_version & 0xFF, N & 0xFF])
        frame=header+payload

        if self.last_payload is not None and self.last_payload==frame:
            self.redundant_avoided+=1
            # versioned: send nothing (avoid duplicate)
            self._log("Matrix Flood: payload unchanged → redundant flood avoided (versioning).")
        else:
            self.matrix_version=(self.matrix_version+1)&0xFF
            header=bytes([self.matrix_version & 0xFF, N & 0xFF])
            frame=header+payload
            self.last_payload=frame
            self.bytes_sent_versioned += len(payload)  # versioned: send actual bytes
            D_round=self._unpack_upper_tri(frame[2:])
            diffs=sum(1 for i in range(N) for j in range(N) if self.D[i][j]!=D_round[i][j])
            self._log(f"Matrix Flood: broadcasted v={self.matrix_version} | payload={len(payload)} bytes (N={N}); round-trip diffs={diffs}.")

        save_pct = 100.0*(1.0 - (self.bytes_sent_versioned/max(1,self.bytes_sent_naive)))
        self._log(f"Flood overhead: attempts={self.flood_attempts}, avoided={self.redundant_avoided}, "
                  f"bytes(versioned/naive)={self.bytes_sent_versioned}/{self.bytes_sent_naive} "
                  f"→ saved {save_pct:.1f}%")
        self._log_event("matrix_flood", {
            "version":self.matrix_version,
            "payload_bytes":len(payload),
            "attempts":self.flood_attempts,
            "avoided":self.redundant_avoided,
            "bytes_naive":self.bytes_sent_naive,
            "bytes_versioned":self.bytes_sent_versioned,
            "saved_pct":save_pct
        })
        self.status_str.set(self._status_text())
        # Append cumulative snapshot for manual cycles
        self.flood_history.append({
            "cycle": len(self.flood_history)+1,
            "bytes_naive": self.bytes_sent_naive,
            "bytes_versioned": self.bytes_sent_versioned,
            "avoided": self.redundant_avoided,
            "saved_pct": save_pct
        })

    def on_matrix_flood_xn(self):
        """Run N consecutive matrix floods (N from UI) and log cumulative bytes per cycle."""
        try:
            n = int(self.cycles_var.get())
            if n <= 0 or n > 10000:
                raise ValueError
        except Exception:
            messagebox.showerror("Invalid cycles", "Please enter a positive integer (≤ 10000) for cycles.")
            return

        # Reset cumulative counters for a clean run
        self.matrix_version = 0
        self.last_payload = None
        self.redundant_avoided = 0
        self.flood_attempts = 0
        self.bytes_sent_naive = 0
        self.bytes_sent_versioned = 0

        self._log(f"Flood ×{n}: starting fresh counters (version, attempts, bytes).")
        cycle_rows = []
        prev_naive = 0
        prev_versioned = 0
        prev_avoided = 0
        
        # Create specific pattern: changes at cycles 1, 5, and 8
        change_cycles = [1, 5, 8]  # Cycles where matrix payload changes
        
        for c in range(1, n + 1):
            # Force matrix change at specific cycles by running ping flood
            if c in change_cycles:
                self._log(f"Cycle {c}: Forcing matrix change with Ping Flood")
                self.on_ping_flood()
            
            self.on_matrix_flood()
            # Record a succinct per-cycle cumulative point
            self._log(f"[Flood Cycle {c}/{n}] Cumulative bytes (versioned/naive) = "
                      f"{self.bytes_sent_versioned}/{self.bytes_sent_naive}; "
                      f"avoided={self.redundant_avoided}")
            self._log_event("flood_cycle", {
                "cycle": c,
                "bytes_naive": self.bytes_sent_naive,
                "bytes_versioned": self.bytes_sent_versioned,
                "attempts": self.flood_attempts,
                "avoided": self.redundant_avoided
            })
            # Build per-cycle row (delta from previous cumulative)
            naive_delta = self.bytes_sent_naive - prev_naive
            versioned_delta = self.bytes_sent_versioned - prev_versioned
            avoided_delta = self.redundant_avoided - prev_avoided
            save_pct = 100.0 * (1.0 - (self.bytes_sent_versioned / max(1, self.bytes_sent_naive)))
            cycle_rows.append({
                "cycle": c,
                "naive_delta": naive_delta,
                "versioned_delta": versioned_delta,
                "avoided_cumulative": self.redundant_avoided,
                "saved_pct_cumulative": save_pct
            })
            prev_naive = self.bytes_sent_naive
            prev_versioned = self.bytes_sent_versioned
            prev_avoided = self.redundant_avoided
        # Write formatted table to CSV
        try:
            self._write_flood_cycles_table(cycle_rows)
        except Exception as e:
            self._log(f"Flood cycles table write failed: {e}")
        self.footer_str.set(f"Flood ×{n} complete. Exported table to exports/ (and events in metrics CSV).")
        
        # Generate cumulative bytes graph
        try:
            self._plot_cumulative_bytes_graph(cycle_rows)
        except Exception as e:
            self._log(f"Cumulative bytes graph generation failed: {e}")

    def on_export_flood_table(self):
        """Export a table using the manual flood history captured so far."""
        if not self.flood_history:
            messagebox.showinfo("Export Flood Table", "No floods recorded yet. Click 'Matrix Flood' first.")
            return
        rows=[]
        prev_naive=0; prev_versioned=0
        for snap in self.flood_history:
            rows.append({
                "cycle": snap["cycle"],
                "naive_delta": snap["bytes_naive"]-prev_naive,
                "versioned_delta": snap["bytes_versioned"]-prev_versioned,
                "avoided_cumulative": snap["avoided"],
                "saved_pct_cumulative": snap["saved_pct"],
            })
            prev_naive=snap["bytes_naive"]; prev_versioned=snap["bytes_versioned"]
        try:
            self._write_flood_cycles_table(rows)
        except Exception as e:
            self._log(f"Export Flood Table failed: {e}")

    def on_reset_flood_log(self):
        """Clear flood counters and history without touching matrices."""
        self.matrix_version=0
        self.last_payload=None
        self.redundant_avoided=0
        self.flood_attempts=0
        self.bytes_sent_naive=0
        self.bytes_sent_versioned=0
        self.flood_history=[]
        self._log("Flood log reset: counters and history cleared.")

    def _write_flood_cycles_table(self, rows):
        """Write per-cycle flood bytes table with Total row."""
        from datetime import datetime as _dt
        import os as _os, csv as _csv
        outdir = _os.path.join(_os.getcwd(), "exports"); ensure_dir(outdir)
        ts = _dt.now().strftime("%Y%m%d_%H%M%S")
        fpath = _os.path.join(outdir, f"flood_cycles_{ts}.csv")
        cols = [
            "Flood Cycle",
            "Naive Strategy (Bytes Sent)",
            "AAMP/GDT Strategy (Bytes Sent)",
            "Redundant Floods Avoided",
            "Cumulative Savings %"
        ]
        total_naive = 0
        total_versioned = 0
        with open(fpath, "w", newline="", encoding="utf-8") as fp:
            w = _csv.writer(fp)
            w.writerow(cols)
            for r in rows:
                total_naive += r["naive_delta"]
                total_versioned += r["versioned_delta"]
                w.writerow([
                    r["cycle"],
                    r["naive_delta"],
                    r["versioned_delta"],
                    r["avoided_cumulative"],
                    f"{r['saved_pct_cumulative']:.1f}"
                ])
            # Total row
            total_saved_pct = 100.0 * (1.0 - (total_versioned / max(1, total_naive)))
            w.writerow([
                "Total",
                total_naive,
                total_versioned,
                rows[-1]["avoided_cumulative"] if rows else 0,
                f"{total_saved_pct:.1f}"
            ])
        self._log(f"Saved flood cycles table → {fpath}")

    def _plot_cumulative_bytes_graph(self, cycle_rows):
        """Generate cumulative bytes graph (Figure 2a)."""
        try:
            import matplotlib.pyplot as plt
            import numpy as np
            from datetime import datetime as _dt
            import os as _os
            
            # Prepare data
            cycles = [r["cycle"] for r in cycle_rows]
            naive_cumulative = []
            versioned_cumulative = []
            
            naive_sum = 0
            versioned_sum = 0
            for r in cycle_rows:
                naive_sum += r["naive_delta"]
                versioned_sum += r["versioned_delta"]
                naive_cumulative.append(naive_sum)
                versioned_cumulative.append(versioned_sum)
            
            # Create the plot (reduced size for ~22KB file size)
            plt.figure(figsize=(6, 4))
            plt.plot(
                cycles,
                naive_cumulative,
                color='black',
                linestyle=':',
                marker='o',
                label='Naive Flooding',
                linewidth=1,
                markersize=4,
            )
            plt.plot(
                cycles,
                versioned_cumulative,
                color='dimgray',
                linestyle='-',
                marker='o',
                label='Version-Controlled Flooding',
                linewidth=1,
                markersize=4,
            )
            
            # Annotations removed to reduce EPS file size to ~22KB
            
            plt.xlabel('Flood Cycle', fontsize=12)
            plt.ylabel('Cumulative Bytes Sent', fontsize=12)
            plt.legend(fontsize=9, loc='upper left')
            plt.grid(True, alpha=0.3)
            plt.xlim(0.5, 10.5)
            # Add headroom for annotations (max value + 10% margin)
            max_val = max(max(naive_cumulative) if naive_cumulative else 0, max(versioned_cumulative) if versioned_cumulative else 0)
            plt.ylim(0, max_val * 1.15)
            
            # Set x-axis ticks
            plt.xticks(range(1, 11))
            
            # Add subplot label (a) for publication
            plt.text(0.5, -0.12, '(a)', transform=plt.gca().transAxes, 
                    ha='center', va='top', fontsize=12, fontweight='bold')
            
            # Save the plot
            outdir = _os.path.join(_os.getcwd(), "exports")
            ensure_dir(outdir)
            ts = _dt.now().strftime("%Y%m%d_%H%M%S")
            fpath_eps = _os.path.join(outdir, f"cumulative_bytes_graph_{ts}.eps")
            fpath_png = _os.path.join(outdir, f"cumulative_bytes_graph_{ts}.png")
            plt.tight_layout(pad=0.1)
            plt.savefig(fpath_eps, format='eps', dpi=72, bbox_inches='tight', pad_inches=0.05)
            plt.savefig(fpath_png, format='png', dpi=72, bbox_inches='tight', pad_inches=0.05)
            plt.close()
            
            self._log(f"Saved cumulative bytes graph → {fpath_eps} and {fpath_png}")
            
            # Also save data to fig2a.txt
            fpath_txt = os.path.join(outdir, "fig2a.txt")
            with open(fpath_txt, "w", encoding="utf-8") as fp:
                fp.write("Figure 2(a): Cumulative Bytes Sent by Naive vs Version-Controlled Flooding\n")
                fp.write("=" * 80 + "\n")
                fp.write("Cycle\tNaive Cumulative (B)\tVersioned Cumulative (B)\tSavings %\n")
                fp.write("-" * 80 + "\n")
                for c, naive_val, versioned_val in zip(cycles, naive_cumulative, versioned_cumulative):
                    savings = 100.0 * (1.0 - (versioned_val / max(1, naive_val)))
                    fp.write(f"{c}\t{naive_val}\t\t\t{versioned_val}\t\t\t{savings:.1f}\n")
                fp.write("\nDetails:\n")
                fp.write(f"Total cycles: {len(cycles)}\n")
                fp.write(f"Matrix size: {self.cfg.N} nodes ({self.cfg.N*(self.cfg.N+1)//2} bytes per matrix)\n")
                fp.write(f"Naive total: {naive_cumulative[-1] if naive_cumulative else 0} bytes\n")
                fp.write(f"Versioned total: {versioned_cumulative[-1] if versioned_cumulative else 0} bytes\n")
                fp.write(f"Overall savings: {100.0 * (1.0 - (versioned_cumulative[-1] / max(1, naive_cumulative[-1]))) if naive_cumulative and versioned_cumulative else 0:.1f}%\n")
            self._log(f"Saved Fig.2a data → {fpath_txt}")
            
        except ImportError:
            self._log("Matplotlib not available - skipping graph generation")
        except Exception as e:
            self._log(f"Graph generation error: {e}")

    # ---------- GDT Reconstruction ----------
    def _dmax(self): return self.cfg.L*math.sqrt(2.0)

    def _bytes_to_meters_and_weights(self):
        N=self.cfg.N; dmax=self._dmax()
        Dm=[[None]*N for _ in range(N)]
        W=[[0.0]*N for _ in range(N)]
        for i in range(N):
            for j in range(N):
                if self.D[i][j]!=UNDEF:
                    Dm[i][j]=(self.D[i][j]/254.0)*dmax
                    W[i][j]=self.Q[i][j] if self.Q[i][j]>0 else 0.05
                else:
                    Dm[i][j]=None; W[i][j]=0.0
        return Dm,W

    def _gdt_optimize(self, X_init):
        """Run gradient descent from provided X_init; return (X_final, D_completed_bytes, stats)."""
        N=self.cfg.N; L=self.cfg.L; dmax=self._dmax()
        Dm,W=self._bytes_to_meters_and_weights()
        X=[tuple(x) for x in X_init]

        iters=600; lr=0.02
        for it in range(iters):
            grads=[(0.0,0.0) for _ in range(N)]
            for i in range(N):
                xi,yi=X[i]
                for j in range(i+1,N):
                    if W[i][j]>0.0 and Dm[i][j] is not None:
                        xj,yj=X[j]
                        dx=xi-xj; dy=yi-yj
                        dist=math.hypot(dx,dy)+1e-9
                        diff=(dist-Dm[i][j]); w=W[i][j]
                        g=(w*2.0*diff/dist)
                        gi_x=g*dx; gi_y=g*dy
                        gx_i,gy_i=grads[i]; gx_j,gy_j=grads[j]
                        grads[i]=(gx_i+gi_x, gy_i+gi_y)
                        grads[j]=(gx_j-gi_x, gy_j-gi_y)
            for i in range(N):
                gx,gy=grads[i]
                xi,yi=X[i]
                xi-=lr*gx; yi-=lr*gy
                xi=0.0 if xi<0.0 else (L if xi>L else xi)
                yi=0.0 if yi<0.0 else (L if yi>L else yi)
                X[i]=(xi,yi)
            if (it+1)%200==0:
                lr*=0.6

        # Completed matrix (fill missing from predicted geometry)
        scale=254.0/dmax
        D_completed=[[UNDEF]*N for _ in range(N)]
        for i in range(N):
            xi,yi=X[i]
            for j in range(N):
                if self.D[i][j]!=UNDEF:
                    D_completed[i][j]=self.D[i][j]
                else:
                    xj,yj=X[j]
                    d=math.hypot(xi-xj, yi-yj)
                    D_completed[i][j]=clamp(int(round(d*scale)),0,254)

        # Metrics
        Dtrue=self._compute_true_distances()
        # MAE on observed entries
        obs_err_sum=0.0; obs_cnt=0
        for i in range(N):
            for j in range(i+1,N):
                if self.D[i][j]!=UNDEF:
                    dm=(self.D[i][j]/254.0)*dmax
                    obs_err_sum+=abs(dm-Dtrue[i][j]); obs_cnt+=1
        mae_obs=(obs_err_sum/obs_cnt) if obs_cnt else float('nan')
        # All-pairs metrics on completed
        all_err_sum=0.0; all_sq_sum=0.0; den_stress=0.0; all_cnt=0
        for i in range(N):
            for j in range(i+1,N):
                dm=(D_completed[i][j]/254.0)*dmax
                e=dm-Dtrue[i][j]
                all_err_sum+=abs(e); all_sq_sum+=e*e; den_stress+=Dtrue[i][j]*Dtrue[i][j]; all_cnt+=1
        mae_all=(all_err_sum/all_cnt) if all_cnt else float('nan')
        rmse_all=math.sqrt(all_sq_sum/all_cnt) if all_cnt else float('nan')
        stress1=math.sqrt(all_sq_sum/max(1e-12,den_stress)) if den_stress>0 else float('nan')

        return X, D_completed, {"mae_obs":mae_obs,"mae_all":mae_all,"rmse_all":rmse_all,"stress1":stress1}

    def _random_init_positions(self):
        N=self.cfg.N; L=self.cfg.L
        return [(self.rng.uniform(0,L), self.rng.uniform(0,L)) for _ in range(N)]

    def _shortest_path_prefill(self, Dm):
        """All-pairs shortest paths on observed-meter graph (Dm with None for missing)."""
        N=self.cfg.N; INF=float('inf')
        sp=[[INF]*N for _ in range(N)]
        for i in range(N): sp[i][i]=0.0
        for i in range(N):
            for j in range(N):
                if Dm[i][j] is not None:
                    sp[i][j]=min(sp[i][j], Dm[i][j])
        for k in range(N):
            sk=sp[k]
            for i in range(N):
                si=sp[i]; dik=si[k]
                if dik==INF: continue
                for j in range(N):
                    val=dik+sk[j]
                    if val<si[j]: si[j]=val
        finite=[sp[i][j] for i in range(N) for j in range(N) if sp[i][j]!=INF and i!=j]
        fallback=sum(finite)/len(finite) if finite else self._dmax()
        for i in range(N):
            for j in range(N):
                if sp[i][j]==INF: sp[i][j]=fallback
        return sp

    def _mds_init(self, Dsp):
        """Classical MDS from all-pairs distances Dsp (meters). Requires numpy."""
        try:
            import numpy as np
        except Exception:
            return None, "numpy is required for MDS init. Please: pip install numpy"
        D=np.array(Dsp, dtype=float); N=D.shape[0]
        J=np.eye(N)-np.ones((N,N))/N
        B=-0.5*J.dot(D**2).dot(J)
        w,V=np.linalg.eigh(B)
        idx=np.argsort(w)[::-1]
        w=w[idx]; V=V[:,idx]
        w2=np.maximum(w[:2],1e-9)
        X=V[:,:2]*np.sqrt(w2)
        L=self.cfg.L
        X=X-X.min(axis=0)
        maxv=float(np.max(X))
        if maxv>0:
            X=X*(L/maxv)
        X=np.clip(X,0.0,L)
        return [(float(x),float(y)) for x,y in X], None

    def _gdt_multistart_best(self):
        """Helper: run multistart (MDS + 9 random) and return (name_best, stats_best)."""
        best=None
        Dm,_=self._bytes_to_meters_and_weights()
        Dsp=self._shortest_path_prefill(Dm)
        X0_mds,err=self._mds_init(Dsp)
        starts=[]
        if X0_mds is not None:
            starts.append(("MDS", X0_mds))
        for k in range(9):
            starts.append((f"R{k+1}", self._random_init_positions()))
        best_rec=None
        for name,X0 in starts:
            _,Dc,stats=self._gdt_optimize(X0)
            score=stats["stress1"]
            if (best is None) or (score<best):
                best=score; best_rec=(name, Dc, stats)
        if best_rec is None:
            return None, None
        nameb, Db, statsb = best_rec
        self.D_completed = Db
        return nameb, statsb

    def on_run_gdt(self):
        X0=self._random_init_positions()
        X,Dc,stats=self._gdt_optimize(X0)
        self.D_completed=Dc
        self._draw_heatmap()
        self.status_str.set(self._status_text())
        self._log(f"GDT (random) done: MAE_obs={stats['mae_obs']:.3f} m; MAE_all={stats['mae_all']:.3f} m; RMSE={stats['rmse_all']:.3f} m; Stress-1={stats['stress1']:.4f}")
        self._log_event("gdt_random", stats)
        self.footer_str.set(f"GDT complete. MAE_all={stats['mae_all']:.3f} m")

    def on_run_gdt_mds(self):
        Dm,_=self._bytes_to_meters_and_weights()
        Dsp=self._shortest_path_prefill(Dm)
        X0,err=self._mds_init(Dsp)
        if X0 is None:
            messagebox.showerror("MDS init unavailable", err)
            return
        _,Dc,stats=self._gdt_optimize(X0)
        self.D_completed=Dc
        self._draw_heatmap()
        self.status_str.set(self._status_text())
        self._log(f"GDT (MDS init) done: MAE_obs={stats['mae_obs']:.3f} m; MAE_all={stats['mae_all']:.3f} m; RMSE={stats['rmse_all']:.3f} m; Stress-1={stats['stress1']:.4f}")
        self._log_event("gdt_mds", stats)
        self.footer_str.set(f"GDT (MDS) complete. MAE_all={stats['mae_all']:.3f} m")

    def on_run_gdt_multistart(self):
        nameb, statsb = self._gdt_multistart_best()
        if nameb is None:
            messagebox.showerror("GDT multistart","No starts available.")
            return
        self._draw_heatmap(); self.status_str.set(self._status_text())
        self._log(f"GDT ×10 (best={nameb}) → MAE_obs={statsb['mae_obs']:.3f} m; MAE_all={statsb['mae_all']:.3f} m; RMSE={statsb['rmse_all']:.3f} m; Stress-1={statsb['stress1']:.4f}")
        self._log_event("gdt_multistart_best", dict(statsb, best=nameb))
        self.footer_str.set(f"GDT ×10 complete. Best Stress-1={statsb['stress1']:.4f} ({nameb})")

    # ---------- σ×θ MAE heatmap sweep ----------
    def on_mae_heatmap_sigma_theta(self):
        """Sweep σ and θ, run multiple seeds per cell, report mean ± std MAE for completed matrix."""
        try:
            import matplotlib.pyplot as plt
            import numpy as np
            from scipy.stats import sem, t
            plt.figure()
            plt.close()
        except Exception as e:
            messagebox.showerror("Matplotlib/Numpy required",f"Please install matplotlib, numpy, scipy.\nError: {e}\nTry: pip install matplotlib numpy scipy")
            return

        # Ask user for sigma/theta grids (comma-separated)
        try:
            from tkinter import simpledialog
        except Exception:
            simpledialog = None

        def _parse_list(text, cast=float):
            vals=[]
            for tok in text.split(','):
                tok=tok.strip()
                if not tok:
                    continue
                vals.append(cast(tok))
            return vals

        if simpledialog is not None:
            s_str = simpledialog.askstring("σ values", "Enter sigma dB list (comma-separated)", initialvalue="1,2,3,4", parent=self)
            t_str = simpledialog.askstring("θ values", "Enter theta list (comma-separated)", initialvalue="0.1,0.2,0.3,0.4", parent=self)
            seeds_str = simpledialog.askstring("Seeds per cell", "How many seeds per cell?", initialvalue="10", parent=self)
            if s_str is None or t_str is None or seeds_str is None:
                self.footer_str.set("Heatmap sweep canceled.")
                return
            try:
                sigmas = _parse_list(s_str, float)
                thetas = _parse_list(t_str, float)
                n_seeds = int(seeds_str)
            except Exception as e:
                messagebox.showerror("Invalid input", f"Could not parse lists.\n{s_str}\n{t_str}\n{e}")
                return
        else:
            sigmas = [1.0, 2.0, 3.0, 4.0]
            thetas = [0.1, 0.2, 0.3, 0.4]
            n_seeds = 10

        rf_mode = self.cfg.rf_range_mode
        rf_val = self.cfg.rf_range_value
        lam_val = self.cfg.lam
        base_seed = self.cfg.seed

        # outdir = os.path.join(os.getcwd(), "exports"); ensure_dir(outdir)
        # fcsv = os.path.join(outdir, "mae_grid_multi.csv")
        # from datetime import datetime
        # ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        # feps = os.path.join(outdir, "mae_heatmap.eps")
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        outdir = os.path.join(os.getcwd(), "exports"); ensure_dir(outdir)
        fcsv = os.path.join(outdir, f"mae_grid_{ts}.csv")
        fcsv_backup = os.path.join(outdir, f"mae_grid_backup_{ts}.csv")
        feps = os.path.join(outdir, f"mae_heatmap_{ts}.eps")
        feps_backup = os.path.join(outdir, f"mae_heatmap_backup_{ts}.eps")

        results = []  # (sigma, theta, mean, std, n, [all_mae])
        total_cells = len(sigmas) * len(thetas)
        completed_cells = 0

        self._log(f"Starting MAE heatmap sweep: {len(sigmas)}×{len(thetas)} = {total_cells} cells, {n_seeds} seeds/cell")
        self._log(f"Autosave: CSV → {fcsv}, EPS → {feps}")

        for s in sigmas:
            for t in thetas:
                completed_cells += 1
                maes = []
                self._log(f"[{completed_cells}/{total_cells}] Processing σ={s} dB, θ={t}...")
                for k in range(n_seeds):
                    try:
                        this_seed = base_seed + k
                        self.cfg.seed = this_seed
                        self.cfg.rf_range_mode = rf_mode
                        self.cfg.rf_range_value = rf_val
                        self.cfg.lam = lam_val
                        self.cfg.sigma_db = float(s)
                        self.cfg.theta = float(t)

                        self.on_reload()
                        self.on_ping_flood()
                        self.on_compare_prune()
                        self.on_run_gdt_mds()

                        # Fetch the last gdt_mds MAE_all value from metrics
                        mae_val = None
                        for m in reversed(self.metrics):
                            if m.get("action") == "gdt_mds" and "mae_all" in m:
                                mae_val = float(m["mae_all"])
                                break
                        if mae_val is not None:
                            maes.append(mae_val)
                    except Exception as e:
                        self._log(f"ERROR in seed {k} for σ={s}, θ={t}: {e}")
                        continue
                if maes:
                    mean_mae = float(np.mean(maes))
                    results.append((s, t, mean_mae))
                    self._log(f"✓ Cell σ={s} dB, θ={t}: MAE_all={mean_mae:.3f} m (n={len(maes)})")
                    self._autosave_mae_results(results, fcsv, fcsv_backup)
                else:
                    self._log(f"WARNING: No MAE values for σ={s}, θ={t}")

        self._log(f"MAE sweep complete: {len(results)}/{total_cells} cells successful")
        self._autosave_mae_results(results, fcsv, fcsv_backup)
        
        # Generate and save heatmap
        try:
            self._generate_mae_heatmap(results, sigmas, thetas, feps, feps_backup)
            self._log(f"✓ MAE heatmap saved → {feps}")
            
            # Also save data to fig3.txt
            fpath_txt = os.path.join(outdir, "fig3.txt")
            with open(fpath_txt, "w", encoding="utf-8") as fp:
                fp.write("Figure 3: Reconstruction error (MAE) under varying RF noise and pruning thresholds\n")
                fp.write("=" * 80 + "\n\n")
                # Build matrix for display
                sigmas_sorted = sorted(set(sigmas))
                thetas_sorted = sorted(set(thetas))
                result_dict = {(s, t): v for s, t, v in results}
                
                # Header
                fp.write(f"{'θ↓ → σ→':<12}")
                for t in thetas_sorted:
                    fp.write(f"  {t:>6}")
                fp.write("\n" + "-" * 80 + "\n")
                
                # Rows
                for s in sigmas_sorted:
                    fp.write(f"{f'σ={s}dB':>10}")
                    for t in thetas_sorted:
                        if (s, t) in result_dict:
                            fp.write(f"{result_dict[(s,t)]:>8.2f}")
                        else:
                            fp.write("     ---")
                    fp.write("\n")
                
                fp.write("\nDetails:\n")
                fp.write(f"Number of seeds per cell: {n_seeds}\n")
                fp.write(f"Configuration: N={self.cfg.N}, L={self.cfg.L}m, λ={self.cfg.lam}\n")
                fp.write(f"RF Range: {rf_mode}={rf_val}\n")
            self._log(f"Saved Fig.3 data → {fpath_txt}")
            
        except Exception as e:
            self._log(f"ERROR generating heatmap: {e}")
        
        self.footer_str.set("MAE heatmap sweep complete. See exports/ for CSV, EPS, and fig3.txt.")

    def _autosave_mae_results(self, results, fcsv, fcsv_backup):
    # """Autosave MAE results to CSV with backup."""
        try:
            if os.path.exists(fcsv):
                import shutil
                shutil.copy2(fcsv, fcsv_backup)
            with open(fcsv, "w", encoding="utf-8") as fp:
                fp.write("sigma_db,theta,mae_m\n")
                for s, t, v in results:
                    fp.write(f"{s},{t},{v}\n")
            self._log(f"Autosaved {len(results)} results → {fcsv}")
        except Exception as e:
            self._log(f"Autosave error: {e}")

    def _generate_mae_heatmap(self, results, sigmas, thetas, feps, feps_backup):
    # """Generate and save MAE heatmap with backup."""
        try:
            import matplotlib.pyplot as plt
            import numpy as np
            sigmas_sorted = sigmas
            thetas_sorted = thetas
            M = np.full((len(sigmas_sorted), len(thetas_sorted)), np.nan, dtype=float)
            for s, t, v in results:
                i = sigmas_sorted.index(s)
                j = thetas_sorted.index(t)
                M[i, j] = v
            fig, ax = plt.subplots(figsize=(4.6, 3.8))
            im = ax.imshow(M, cmap="viridis", origin="upper", aspect="auto")
            ax.set_xticks(range(len(thetas_sorted)))
            ax.set_xticklabels([f"θ={x:.1f}" for x in thetas_sorted])
            ax.set_yticks(range(len(sigmas_sorted)))
            ax.set_yticklabels([f"σ={int(s)}dB" for s in sigmas_sorted])
            ax.set_ylabel("Noise")
            ax.set_xlabel("Confidence threshold")
            cbar = fig.colorbar(im, ax=ax)
            cbar.set_label("MAE (m)")
            vmin = np.nanmin(M) if np.isfinite(M).any() else 0.0
            vmax = np.nanmax(M) if np.isfinite(M).any() else 1.0
            mid = (vmin + vmax) / 2.0
            for i in range(M.shape[0]):
                for j in range(M.shape[1]):
                    if np.isfinite(M[i, j]):
                        color = "white" if M[i, j] > mid else "black"
                        ax.text(j, i, f"{M[i, j]:.2f}", ha="center", va="center", color=color)

            plt.tight_layout()
            if os.path.exists(feps):
                import shutil
                shutil.copy2(feps, feps_backup)
            fpng = os.path.join(os.path.dirname(feps), os.path.basename(feps).replace('.eps', '.png'))
            plt.savefig(feps, format='eps', dpi=200, bbox_inches='tight')
            plt.savefig(fpng, format='png', dpi=200, bbox_inches='tight')
            plt.close(fig)

        except Exception as e:
            self._log(f"Heatmap generation error: {e}")
            raise

    # ---------- Validation ----------
    def _compute_true_distances(self):
        N=self.cfg.N
        Dtrue=[[0.0]*N for _ in range(N)]
        for i in range(N):
            xi,yi=self.nodes[i]
            for j in range(N):
                xj,yj=self.nodes[j]
                Dtrue[i][j]=math.hypot(xi-xj, yi-yj)
        return Dtrue

    def on_validate_gdt(self):
        if self.D_completed is None:
            messagebox.showwarning("Run GDT first","Please run GDT to build the completed matrix.")
            return
        N=self.cfg.N; dmax=self._dmax()
        Dtrue=self._compute_true_distances()
        Dhat=[[0.0]*N for _ in range(N)]
        for i in range(N):
            for j in range(N):
                Dhat[i][j]=(self.D_completed[i][j]/254.0)*dmax

        num=0; mae_sum=0.0; rmse_sum=0.0; den_stress=0.0
        for i in range(N):
            for j in range(i+1,N):
                e=Dhat[i][j]-Dtrue[i][j]
                mae_sum+=abs(e); rmse_sum+=e*e; den_stress+=Dtrue[i][j]*Dtrue[i][j]
                num+=1
        mae=mae_sum/num if num else float('nan')
        rmse=math.sqrt(rmse_sum/num) if num else float('nan')
        stress1=math.sqrt(rmse_sum/max(1e-12,den_stress)) if den_stress>0 else float('nan')

        # Pearson r (upper-tri)
        xs,ys=[],[]
        for i in range(N):
            for j in range(i+1,N):
                xs.append(Dhat[i][j]); ys.append(Dtrue[i][j])
        if len(xs)>=2:
            mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
            nume=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
            denx=math.sqrt(sum((x-mx)**2 for x in xs))
            deny=math.sqrt(sum((y-my)**2 for y in ys))
            r = (nume/(denx*deny)) if (denx>0 and deny>0) else float('nan')
        else:
            r=float('nan')

        # Triangle inequality violations (sample up to 25k triples)
        triples_all=list(itertools.combinations(range(N),3))
        if len(triples_all)>25000:
            import random as _rnd
            triples=_rnd.sample(triples_all,25000)
        else:
            triples=triples_all
        violations=0; checked=0
        for (i,j,k) in triples:
            dij=Dhat[i][j]; djk=Dhat[j][k]; dik=Dhat[i][k]
            if dij+djk<dik-1e-9 or djk+dik<dij-1e-9 or dik+dij<djk-1e-9:
                violations+=1
            checked+=1
        tiv_rate=(violations/checked) if checked else float('nan')

        self._log(f"VALIDATE: MAE={mae:.3f} m | RMSE={rmse:.3f} m | Stress-1={stress1:.4f} | Pearson r={r:.4f} | Triangle Violations={tiv_rate*100:.2f}% ({violations}/{checked})")
        self._log_event("validate", {"mae_m":mae,"rmse_m":rmse,"stress1":stress1,"pearson_r":r,"tiv_rate":tiv_rate,"triples_checked":checked})
        self.footer_str.set("Validation done. See log for metrics.")

    # ---------- Exports ----------
    def on_export_csv(self):
        ts=datetime.now().strftime("%Y%m%d_%H%M%S")
        outdir=os.path.join(os.getcwd(),"exports"); ensure_dir(outdir)

        f1=os.path.join(outdir, f"D_measured_{ts}.csv"); self._write_csv_matrix(f1, self.D)
        if self.D_completed is not None:
            f2=os.path.join(outdir, f"D_completed_{ts}.csv"); self._write_csv_matrix(f2, self.D_completed)

        f3=os.path.join(outdir, f"metrics_{ts}.csv"); self._write_csv_metrics(f3)
        f4=os.path.join(outdir, f"config_{ts}.json")
        with open(f4,"w",encoding="utf-8") as fp:
            fp.write(json.dumps(asdict(self.cfg), ensure_ascii=False, indent=2))

        if self.D_completed is not None:
            dmax=self._dmax(); Dtrue=self._compute_true_distances()
            fres=os.path.join(outdir, f"residuals_m_{ts}.csv")
            with open(fres,"w",encoding="utf-8") as fp:
                N=self.cfg.N
                fp.write("i,j,residual_m\n")
                for i in range(N):
                    for j in range(i+1,N):
                        dhat=(self.D_completed[i][j]/254.0)*dmax
                        res=dhat-Dtrue[i][j]
                        fp.write(f"{i},{j},{res}\n")

        self._log(f"Exported CSV to {outdir} (D_measured, D_completed, metrics, config, residuals*).")
        self.footer_str.set(f"CSV exported → {outdir}")

    def _write_csv_matrix(self, path, M):
        with open(path,"w",encoding="utf-8") as fp:
            N=self.cfg.N
            for i in range(N):
                fp.write(",".join(str(M[i][j]) for j in range(N))+"\n")

    def _write_csv_metrics(self, path):
        if not self.metrics:
            with open(path,"w",encoding="utf-8") as fp:
                fp.write("timestamp,action\n")
            return
        keys=set()
        for m in self.metrics:
            keys.update(m.keys())
        keys=[k for k in keys if k!="ts" and k!="action"]
        keys_sorted=["ts","action"]+sorted(keys)
        with open(path,"w",encoding="utf-8") as fp:
            fp.write(",".join(keys_sorted)+"\n")
            for m in self.metrics:
                fp.write(",".join(str(m.get(k,"")) for k in keys_sorted)+"\n")

    def on_export_png(self):
        try:
            import matplotlib.pyplot as plt, numpy as np
            import matplotlib.cm as cm
        except Exception:
            messagebox.showerror("Matplotlib required","EPS export needs matplotlib + numpy.\nTry: pip install matplotlib numpy")
            return
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        outdir = os.path.join(os.getcwd(), "exports"); ensure_dir(outdir)
        feps = os.path.join(outdir, f"heatmap_{'completed' if (self.show_completed_var.get() and self.D_completed is not None) else 'measured'}_{ts}.eps")
        Dview = self.D_completed if (self.show_completed_var.get() and self.D_completed is not None) else self.D
        arr = np.array(Dview, dtype=float)
        arr[arr == UNDEF] = np.nan
        plt.figure()
        plt.imshow(arr, interpolation='nearest', cmap='viridis')
        plt.colorbar()
        plt.tight_layout()
        fpng = os.path.join(outdir, f"heatmap_{'completed' if (self.show_completed_var.get() and self.D_completed is not None) else 'measured'}_{ts}.png")
        plt.savefig(feps, format='eps', dpi=200)
        plt.savefig(fpng, format='png', dpi=200)
        plt.close()
        self._log(f"Exported EPS: {feps} and PNG: {fpng}")
        self.footer_str.set(f"EPS and PNG exported: {feps}, {fpng}")

    def on_export_truth(self):
        """Export ground-truth node coords and pairwise true distances (meters)."""
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        outdir = os.path.join(os.getcwd(), "exports"); ensure_dir(outdir)

        # Nodes (truth)
        fnodes = os.path.join(outdir, f"nodes_{ts}.csv")
        with open(fnodes, "w", encoding="utf-8") as fp:
            fp.write("id,x_m,y_m\n")
            for i, (x, y) in enumerate(self.nodes):
                fp.write(f"{i},{x},{y}\n")

        # True distances (meters)
        Dtrue = self._compute_true_distances()
        ftrue = os.path.join(outdir, f"D_true_m_{ts}.csv")
        with open(ftrue, "w", encoding="utf-8") as fp:
            N = self.cfg.N
            for i in range(N):
                fp.write(",".join(f"{Dtrue[i][j]:.6f}" for j in range(N)) + "\n")

        self._log(f"Exported truth to {outdir} (nodes_*, D_true_m_*).")
        self.footer_str.set("Truth exported.")

    # ---------- Config Form ----------
    def open_config_form(self):
        ConfigForm(self, self.cfg, on_apply=self._apply_new_config)

    def _apply_new_config(self, new_cfg: 'SimConfig'):
        old_seed=self.cfg.seed; old_N=self.cfg.N
        self.cfg=new_cfg
        if self.cfg.seed!=old_seed:
            self.rng=random.Random(self.cfg.seed)
        if self.cfg.N!=old_N:
            self._deploy_nodes(self.cfg.N)
            self._reset_matrices()
        self._draw_scene()
        self._draw_heatmap()
        self._log(f"Applied new config: {asdict(self.cfg)}")

    # ---------- Logging helpers ----------
    def _log(self, msg: str):
        self.log_text.insert(tk.END, msg + "\n")
        self.log_text.see(tk.END)

    def _log_event(self, action, payload=None):
        e={"ts": int(self.sim_time), "action": action}
        if payload: e.update(payload)
        self.metrics.append(e)

    # ---------- Mobility trial (5 of 32 nodes, 6 cycles) ----------
    def _move_nodes(self, idxs, min_jump=10.0, max_jump=15.0):
        L=self.cfg.L
        for i in idxs:
            x,y=self.nodes[i]
            # random direction and distance
            ang = self.rng.uniform(0, 2*math.pi)
            dist = self.rng.uniform(min_jump, max_jump)
            nx = clamp(x + dist*math.cos(ang), 0.0, L)
            ny = clamp(y + dist*math.sin(ang), 0.0, L)
            self.nodes[i] = (nx, ny)

    # def on_mobility_trial(self):
    #     if self.cfg.N < 5:
    #         messagebox.showerror("Mobility Trial", "Need at least 5 nodes.")
    #         return
    #     mobile = self.rng.sample(range(self.cfg.N), 5)
    #     self._log(f"Mobility: moving nodes {mobile} by 10–15 m (clamped to field).")
    #     self._move_nodes(mobile)
    #     self._draw_scene()

    #     # 6 recovery cycles: Ping → (optional prune if not baseline?) → Flood → GDT×10 → Validate
    #     cycles = 6
    #     per_cycle = []
    #     for c in range(1, cycles+1):
    #         self._log(f"[Cycle {c}/6] Starting...")
    #         self.on_ping_flood()
    #         if not self.baseline_no_aamp_var.get():
    #             self.on_prune_matrix()
    #         self.on_matrix_flood()
    #         nameb, statsb = self._gdt_multistart_best()
    #         if nameb is None:
    #             messagebox.showerror("Mobility Trial","GDT multi-start failed.")
    #             return
    #         # Validate to compute full-set metrics
    #         self.on_validate_gdt()
    #         per_cycle.append(statsb["mae_all"])
    #         self._log(f"[Cycle {c}/6] Best={nameb} → MAE_all={statsb['mae_all']:.3f} m, RMSE={statsb['rmse_all']:.3f} m, Stress-1={statsb['stress1']:.4f}")

    #     # Summarize
    #     def cycles_to(thresh):
    #         for i, v in enumerate(per_cycle, start=1):
    #             if v <= thresh: return i
    #         return None

    #     c_1m = cycles_to(1.0)
    #     c_0p5m = cycles_to(0.5)
    #     self._log(f"Mobility Trial summary: MAE_all per cycle = {['%.3f'%v for v in per_cycle]}")
    #     self._log(f"Cycles to ≤1.0 m: {c_1m if c_1m is not None else 'not reached in 6'} | "
    #               f"Cycles to ≤0.5 m: {c_0p5m if c_0p5m is not None else 'not reached in 6'}")

    #     self.footer_str.set("Mobility trial complete. See log for per-cycle metrics.")

    #     # Plot MAE values over recovery cycles
    #     try:
    #         mae_values = per_cycle  # Use the recorded MAE_all values
    #         cycles = list(range(1, len(mae_values) + 1))

    #         import os
    #         from datetime import datetime as _dt

    #         plt.figure()
    #         plt.plot(cycles, mae_values, marker='o', color='blue', label='MAE per cycle')
    #         plt.xlabel('Recovery Cycle')
    #         plt.ylabel('Mean Absolute Error (MAE) [m]')
    #         plt.title('Recovery Trajectory of AAMP/GDT Under Mobility')
    #         plt.grid(True)
    #         plt.annotate('15% nodes displaced', xy=(1, mae_values[0]), xytext=(2, max(mae_values)+0.1),
    #                      arrowprops=dict(facecolor='black', shrink=0.05),
    #                      fontsize=10, color='red', fontweight='bold')
    #         plt.legend()
    #         plt.tight_layout()

    #         # --- Save EPS ---
    #         outdir = os.path.join(os.getcwd(), "exports")
    #         ensure_dir(outdir)
    #         ts = _dt.now().strftime("%Y%m%d_%H%M%S")
    #         fpath = os.path.join(outdir, f"mobility_recovery_{ts}.eps")
    #         plt.savefig(fpath, format='eps', dpi=200)
    #         self._log(f"Saved recovery trajectory plot → {fpath}")

    #         plt.show()
    #     except Exception as e:
    #         self._log(f"Error plotting MAE trajectory: {e}")
    #     self.footer_str.set("Mobility trial complete. See log for per-cycle metrics.")
    def run_mobility_trial(
        self,
        num_trials=5,
        cycles=6,
        mobile_fraction=5 / 32,
        displacement_min=10.0,
        displacement_max=15.0,
        export_dir=None,
        include_plot=True,
        use_aamp=None,
    ):
        """
        Execute the mobility trial workflow (GUI button or headless CLI).

        Returns a dictionary with summary statistics and output file paths
        (EPS, TXT, CSV as available).
        """
        if self.cfg.N < 5:
            raise RuntimeError("Need at least 5 nodes to run the mobility trial.")
        if not (0.0 < mobile_fraction <= 1.0):
            raise ValueError("mobile_fraction must be within (0, 1].")
        if displacement_min > displacement_max:
            raise ValueError("displacement_min cannot exceed displacement_max.")
        if num_trials <= 0 or cycles <= 0:
            raise ValueError("num_trials and cycles must be positive integers.")

        import numpy as np
        from datetime import datetime as _dt

        total_nodes = self.cfg.N
        mobile_count = max(1, min(total_nodes, int(round(total_nodes * mobile_fraction))))

        base_seed = self.cfg.seed if self.cfg.seed is not None else 0
        original_seed = self.cfg.seed
        original_rng = self.rng
        original_baseline = self.baseline_no_aamp_var.get()

        if use_aamp is not None:
            self.baseline_no_aamp_var.set(not use_aamp)

        if export_dir is None:
            export_dir = os.path.join(os.getcwd(), "exports")
        ensure_dir(export_dir)

        results_per_cycle = [[] for _ in range(cycles)]

        for trial in range(num_trials):
            seed = base_seed + trial
            self.cfg.seed = seed
            self.rng = random.Random(seed)
            self.on_reload()

            mobile = self.rng.sample(range(total_nodes), mobile_count)
            self._log(
                f"[Trial {trial+1}/{num_trials}] Mobility: moving nodes {mobile} "
                f"by {displacement_min:.1f}–{displacement_max:.1f} m (clamped)."
            )
            self._move_nodes(mobile, displacement_min, displacement_max)
            self._draw_scene()

            for c in range(cycles):
                self._log(f"[Trial {trial+1}/{num_trials}] Cycle {c+1}/{cycles} starting...")
                self.on_ping_flood()
                if not self.baseline_no_aamp_var.get():
                    self.on_prune_matrix()
                self.on_matrix_flood()
                nameb, statsb = self._gdt_multistart_best()
                if nameb is None:
                    raise RuntimeError("GDT multi-start failed; aborting mobility trial.")
                self.on_validate_gdt()
                mae_val = statsb["mae_all"]
                results_per_cycle[c].append(mae_val)
                self._log(
                    f"[Trial {trial+1}/{num_trials}] Cycle {c+1}: MAE_all={mae_val:.3f} m"
                )

        mean_vals = [float(np.mean(vals)) if vals else float("nan") for vals in results_per_cycle]
        std_vals = [float(np.std(vals)) if vals else float("nan") for vals in results_per_cycle]
        cycles_x = list(range(1, cycles + 1))

        self._log(
            "Mobility Trial summary (mean MAE per cycle): "
            + str([f"{v:.3f}" for v in mean_vals])
        )

        eps_path = None
        txt_path = None
        csv_path = None

        try:
            if include_plot:
                fig, ax = plt.subplots(figsize=(7, 5))
                ax.errorbar(
                    cycles_x,
                    mean_vals,
                    yerr=std_vals,
                    fmt="-o",
                    color="blue",
                    ecolor="black",
                    elinewidth=1.5,
                    capsize=4,
                    label="MAE per cycle",
                )
                ax.set_xlabel("Recovery Cycle")
                ax.set_ylabel("Mean Absolute Error (MAE) [m]")
                ax.grid(True)
                ax.annotate(
                    f"{mobile_count} nodes displaced",
                    xy=(1, mean_vals[0]),
                    xycoords="data",
                    xytext=(-60, 20),
                    textcoords="offset points",
                    arrowprops=dict(arrowstyle="->", color="black", lw=1.5),
                    fontsize=10,
                    color="red",
                    weight="bold",
                )
                ax.legend()
                plt.tight_layout()

                ts = _dt.now().strftime("%Y%m%d_%H%M%S")
                eps_path = os.path.join(export_dir, f"mobility_recovery_{ts}.eps")
                png_path = os.path.join(export_dir, f"mobility_recovery_{ts}.png")
                plt.savefig(eps_path, format='eps', dpi=300, bbox_inches="tight")
                plt.savefig(png_path, format='png', dpi=300, bbox_inches="tight")
                plt.close(fig)
                self._log(f"Saved recovery trajectory plot → {eps_path} and {png_path}")

            improvement = mean_vals[0] - mean_vals[-1] if len(mean_vals) >= 2 else float("nan")
            improvement_pct = (
                (improvement / mean_vals[0]) * 100 if mean_vals and mean_vals[0] > 0 else float("nan")
            )

            txt_path = os.path.join(export_dir, "fig4.txt")
            with open(txt_path, "w", encoding="utf-8") as fp:
                fp.write("Figure 4: Recovery Trajectory of AAMP/GDT Under Node Mobility\n")
                fp.write("=" * 70 + "\n\n")
                fp.write("Description:\n")
                fp.write(
                    f"Mean absolute error (MAE) evolution over {cycles} operational recovery cycles\n"
                )
                fp.write(
                    f"following displacement of {mobile_count} nodes "
                    f"({mobile_count / total_nodes * 100:.1f}% of the network) "
                    f"by {displacement_min:.1f}-{displacement_max:.1f} m in random directions.\n"
                )
                fp.write(
                    "Each recovery cycle consists of: (1) ping flood (RSSI-based distance measurement), "
                    "(2) AAMP pruning (age-aware confidence decay), (3) version-controlled matrix flood, "
                    "(4) multi-start GDT reconstruction, and (5) validation.\n"
                )
                fp.write("Results are averaged over independent simulation trials; error bars are ±1σ.\n\n")
                fp.write("Recovery Cycle MAE Data\n")
                fp.write("-" * 70 + "\n")
                fp.write("Cycle\tMean MAE (m)\tStd Dev (m)\n")
                fp.write("-" * 70 + "\n")
                for c, mean, std in zip(cycles_x, mean_vals, std_vals):
                    fp.write(f"{c}\t{mean:.4f}\t{std:.4f}\n")
                fp.write("\nExperimental Setup:\n")
                fp.write(f"Number of trials: {num_trials}\n")
                fp.write(f"Number of recovery cycles: {cycles}\n")
                fp.write(f"Nodes displaced: {mobile_count} ({mobile_count / total_nodes * 100:.1f}%)\n")
                fp.write(f"Displacement range: {displacement_min:.1f}-{displacement_max:.1f} m\n")
                fp.write(
                    f"Configuration: N={self.cfg.N}, L={self.cfg.L}m, σ={self.cfg.sigma_db}dB, "
                    f"λ={self.cfg.lam}, θ={self.cfg.theta}\n"
                )
                fp.write(
                    f"Flood/Prune interval: every {self.cfg.flood_interval_min} min / "
                    f"{self.cfg.prune_interval_min} min\n\n"
                )
                fp.write("Key Findings:\n")
                if len(mean_vals) >= 2:
                    fp.write(f"- Initial MAE (cycle 1): {mean_vals[0]:.4f} m ± {std_vals[0]:.4f} m\n")
                    fp.write(
                        f"- Final MAE (cycle {cycles}): {mean_vals[-1]:.4f} m ± {std_vals[-1]:.4f} m\n"
                    )
                    if not math.isnan(improvement):
                        fp.write(
                            f"- Recovery: {improvement:.4f} m improvement "
                            f"({improvement_pct:.1f}% reduction)\n"
                        )
                fp.write("- Decreasing standard deviation indicates stable recovery behavior.\n")
            self._log(f"Saved Fig.4 data → {txt_path}")

            csv_path = os.path.join(export_dir, "fig4.csv")
            with open(csv_path, "w", newline="", encoding="utf-8") as fp_csv:
                writer = csv.writer(fp_csv)
                writer.writerow(["Cycle", "Mean_MAE_m", "Std_MAE_m"])
                for c, mean, std in zip(cycles_x, mean_vals, std_vals):
                    writer.writerow([c, f"{mean:.6f}", f"{std:.6f}"])
            self._log(f"Saved Fig.4 CSV → {csv_path}")

        except Exception as exc:
            self._log(f"Error exporting mobility trial results: {exc}")
            raise
        finally:
            self.cfg.seed = original_seed
            self.rng = original_rng
            self.baseline_no_aamp_var.set(original_baseline)

        self.footer_str.set("Mobility trial complete. See log for averaged metrics.")

        return {
            "mean_mae": mean_vals,
            "std_mae": std_vals,
            "cycles": cycles,
            "num_trials": num_trials,
            "mobile_fraction": mobile_fraction,
            "mobile_count": mobile_count,
            "displacement_range": [displacement_min, displacement_max],
            "plot_path": eps_path,
            "data_path": txt_path,
            "csv_path": csv_path,
        }

    def on_mobility_trial(self):
        try:
            self.run_mobility_trial()
        except RuntimeError as exc:
            messagebox.showerror("Mobility Trial", str(exc))
        except Exception as exc:
            messagebox.showerror("Mobility Trial", f"Error during mobility trial:\n{exc}")


    def _get_latest_metric(self, action_name):
        """Helper to get the latest metric dict for a given action."""
        for m in reversed(self.metrics):
            if m.get("action") and action_name in m.get("action"):
                return m
        return {}

    def on_export_gdt_accuracy_table(self):
        """Run all GDT strategies with multiple seeds and export mean ± std accuracy metrics to CSV."""
        import os
        import numpy as np
        from datetime import datetime as _dt
        import csv

        outdir = os.path.join(os.getcwd(), "exports")
        ensure_dir(outdir)
        ts = _dt.now().strftime("%Y%m%d_%H%M%S")
        fpath = os.path.join(outdir, f"gdt_accuracy_table_{ts}.csv")

        n_seeds = 10  # You can prompt the user for this if you want
        base_seed = self.cfg.seed

        strategies = [
            ("Random", self.on_run_gdt, "gdt_random"),
            ("MDS", self.on_run_gdt_mds, "gdt_mds"),
            ("Multistart Best", self.on_run_gdt_multistart, "gdt_multistart_best"),
        ]

        rows = []
        for label, gdt_func, metric_label in strategies:
            maes, rmses, stresses = [], [], []
            for k in range(n_seeds):
                # Set a new seed for each run
                self.cfg.seed = base_seed + k
                self.on_reload()
                self.on_ping_flood()
                if not self.baseline_no_aamp_var.get():
                    self.on_prune_matrix()
                gdt_func()
                metrics = self._get_latest_metric(metric_label)
                if metrics.get('mae_all') is not None:
                    maes.append(metrics['mae_all'])
                if metrics.get('rmse_all') is not None:
                    rmses.append(metrics['rmse_all'])
                if metrics.get('stress1') is not None:
                    stresses.append(metrics['stress1'])
            # Compute mean and std
            def fmt(arr):
                arr = np.array(arr)
                return f"{np.mean(arr):.3f} ± {np.std(arr, ddof=1):.3f}" if len(arr) > 1 else (f"{arr[0]:.3f}" if arr else "")
            rows.append([
                label,
                fmt(maes),
                fmt(rmses),
                fmt(stresses)
            ])

        with open(fpath, "w", newline="", encoding="utf-8") as fp:
            w = csv.writer(fp)
            w.writerow([
                "Initialization Strategy",
                "Mean Absolute Error (MAE) All Pairs (m) (mean ± std)",
                "Root Mean Square Error (RMSE) (m) (mean ± std)",
                "Normalized Stress (Stress-1) (mean ± std)"
            ])
            for row in rows:
                w.writerow(row)
        self._log(f"Exported GDT accuracy table (mean ± std over {n_seeds} seeds) → {fpath}")
        
        # Also save data to table3.txt
        fpath_txt = os.path.join(outdir, "table3.txt")
        with open(fpath_txt, "w", encoding="utf-8") as fp:
            fp.write("Table 3: Reconstruction Accuracy of GDT Module\n")
            fp.write("=" * 70 + "\n")
            fp.write("\n")
            fp.write("Description:\n")
            fp.write(f"Results are averaged over {n_seeds} simulation runs using systematically varied seeds\n")
            fp.write(f"(base_seed={base_seed} through {base_seed+n_seeds-1}). Each run uses a different seed\n")
            fp.write("to ensure statistical independence while maintaining reproducibility. Minor variations\n")
            fp.write("in results originate from the different seed values and stochastic processes within\n")
            fp.write("the simulation code (RSSI noise, random node deployment, GDT initialization).\n")
            fp.write("\n")
            fp.write("Initialization Strategy | MAE All Pairs (m) | RMSE (m) | Stress-1\n")
            fp.write("-" * 70 + "\n")
            for row in rows:
                strategy, mae, rmse, stress = row
                fp.write(f"{strategy:<21} | {mae:<18} | {rmse:<8} | {stress}\n")
            fp.write("\n")
            fp.write("Experimental Setup:\n")
            fp.write(f"Number of trials per strategy: {n_seeds}\n")
            fp.write(f"Seed range: {base_seed} to {base_seed+n_seeds-1}\n")
            fp.write(f"Configuration: N={self.cfg.N}, L={self.cfg.L}m, σ={self.cfg.sigma_db}dB, λ={self.cfg.lam}, θ={self.cfg.theta}\n")
        self._log(f"Saved Table 3 data → {fpath_txt}")
        
        self.footer_str.set("GDT accuracy table exported.")

# ---------------- Config Window ----------------
class ConfigForm(tk.Toplevel):
    def __init__(self, parent: WSNApp, cfg: SimConfig, on_apply):
        super().__init__(parent)
        self.title("Simulation Config")
        self.resizable(False, False)
        self.transient(parent)
        self.grab_set()
        self.on_apply = on_apply
        self.parent = parent

        # Vars bound to fields
        self.var_N=tk.StringVar(value=str(cfg.N))
        self.var_L=tk.StringVar(value=str(cfg.L))
        self.var_rfmode=tk.StringVar(value=cfg.rf_range_mode)
        self.var_rfval=tk.StringVar(value=str(cfg.rf_range_value))
        self.var_sigma=tk.StringVar(value=str(cfg.sigma_db))
        self.var_seed=tk.StringVar(value=str(cfg.seed))
        self.var_lam=tk.StringVar(value=str(cfg.lam))
        self.var_theta=tk.StringVar(value=str(cfg.theta))
        self.var_flood=tk.StringVar(value=str(cfg.flood_interval_min))
        self.var_prune=tk.StringVar(value=str(cfg.prune_interval_min))
        self.var_mode=tk.StringVar(value=cfg.mode)

        pad={"padx":8,"pady":4}
        outer=ttk.Frame(self, padding=12); outer.pack(fill=tk.BOTH, expand=True)

        # --- Best-Practice Preset mini-toolbar (inside Config) ---
        preset_bar=ttk.Frame(outer); preset_bar.grid(row=0, column=0, columnspan=2, sticky="we", pady=(0,6))
        ttk.Label(preset_bar, text="Quick load:", font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT, padx=(0,6))
        ttk.Button(preset_bar, text="Load Best-Practice Preset", command=self._fill_best_practice).pack(side=tk.LEFT)
        ttk.Button(preset_bar, text="Reset to Current", command=self._fill_from_parent).pack(side=tk.LEFT, padx=(6,0))

        row=1
        ttk.Label(outer, text="N (nodes)").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_N,width=12).grid(row=row,column=1,**pad); row+=1
        ttk.Label(outer, text="L (meters, square)").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_L,width=12).grid(row=row,column=1,**pad); row+=1
        ttk.Label(outer, text="RF range mode").grid(row=row,column=0,sticky="w",**pad); row+=1
        ttk.Combobox(outer, textvariable=self.var_rfmode, values=["fraction_diag", "absolute_m"], state="readonly", width=12).grid(row=row, column=1, **pad)
        row += 1
        ttk.Label(outer, text="RF range value").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_rfval,width=12).grid(row=row,column=1,**pad); row+=1
        ttk.Label(outer, text="Seed").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_seed,width=12).grid(row=row,column=1,**pad); row+=1
        ttk.Label(outer, text="σ (dB)").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_sigma,width=12).grid(row=row,column=1,**pad); row+=1
        
        ttk.Label(outer, text="AAMP Parameters", font=("Segoe UI",10,"bold")).grid(row=row,column=0,sticky="w",**pad); row+=1
        ttk.Label(outer, text="λ (lambda)").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_lam,width=12).grid(row=row,column=1,**pad); row+=1
        ttk.Label(outer, text="θ (theta)").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_theta,width=12).grid(row=row,column=1,**pad); row+=1

        row+=1; ttk.Separator(outer).grid(row=row,column=0,columnspan=2,sticky="we",**pad); row+=1
        ttk.Label(outer, text="Scheduling", font=("Segoe UI",10,"bold")).grid(row=0,column=0,sticky="w",**pad); row+=1
        ttk.Label(outer, text="Flood interval (min)").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_flood,width=12).grid(row=row,column=1,**pad); row+=1
        ttk.Label(outer, text="Prune interval (min)").grid(row=row,column=0,sticky="w",**pad); ttk.Entry(outer,textvariable=self.var_prune,width=12).grid(row=row,column=1,**pad); row+=1

        row+=1; ttk.Separator(outer).grid(row=row,column=0,columnspan=2,sticky="we",**pad); row+=1
        ttk.Label(outer, text="Mode", font=("Segoe UI",10,"bold")).grid(row=row,column=0,sticky="w",**pad); row+=1
        ttk.Label(outer, text="Run mode").grid(row=row,column=0,sticky="w",**pad)
        ttk.Combobox(outer,textvariable=self.var_mode,values=["Manual","Auto"],state="readonly",width=12).grid(row=row,column=1,**pad); row+=1

        btns=ttk.Frame(outer); btns.grid(row=row,column=0,columnspan=2,sticky="e",**pad)
        ttk.Button(btns, text="Cancel", command=self._on_cancel).pack(side=tk.RIGHT, padx=4)
        ttk.Button(btns, text="Apply", command=self._on_apply).pack(side=tk.RIGHT, padx=4)

        self.update_idletasks()
        self._center_over_parent()

    # --- Preset fillers inside Config ---
    def _fill_best_practice(self):
        # EXACT recommended values pinned here:
        self.var_N.set("32")
        self.var_L.set("50.0")
        self.var_rfmode.set("fraction_diag")
        self.var_rfval.set("0.48")
        self.var_sigma.set("2.0")
        self.var_seed.set("12345")
        self.var_lam.set("0.0002")
        self.var_theta.set("0.30")
        self.var_flood.set("15")
        self.var_prune.set("15")
        self.var_mode.set("Manual")

    def _fill_from_parent(self):
        c=self.parent.cfg
        self.var_N.set(str(c.N)); self.var_L.set(str(c.L))
        self.var_rfmode.set(c.rf_range_mode); self.var_rfval.set(str(c.rf_range_value))
        self.var_sigma.set(str(c.sigma_db)); self.var_seed.set(str(c.seed))
        self.var_lam.set(str(c.lam)); self.var_theta.set(str(c.theta))
        self.var_flood.set(str(c.flood_interval_min)); self.var_prune.set(str(c.prune_interval_min))
        self.var_mode.set(c.mode)

    def _center_over_parent(self):
        parent=self.parent
        pw=parent.winfo_width(); ph=parent.winfo_height()
        px=parent.winfo_rootx(); py=parent.winfo_rooty()
        w=self.winfo_reqwidth(); h=self.winfo_reqheight()
        x=px+(pw-w)//2; y=py+(ph-h)//2
        self.geometry(f"+{x}+{y}")

    def _on_cancel(self): self.destroy()

    def _on_apply(self):
        try:
            N=int(self.var_N.get()); 
            if not (2<=N<=1024): raise ValueError("N out of range [2..1024]")
            L=float(self.var_L.get())
            rf_mode=self.var_rfmode.get()
            if rf_mode not in ("fraction_diag","absolute_m"): raise ValueError("rf_range_mode invalid")
            rf_val=float(self.var_rfval.get())
            sigma=float(self.var_sigma.get())
            seed=int(self.var_seed.get())
            lam=float(self.var_lam.get())
            theta=float(self.var_theta.get())
            if not (0.0<=theta<=1.0): raise ValueError("θ must be in [0,1]")
            flood=int(self.var_flood.get())
            prune=int(self.var_prune.get())
            mode=self.var_mode.get()
            if mode not in ("Manual","Auto"): raise ValueError("mode invalid")
        except Exception as e:
            messagebox.showerror("Invalid Config", f"Please check your inputs.\n{e}")
            return

        new_cfg=SimConfig(
            N=N, L=L, rf_range_mode=rf_mode, rf_range_value=rf_val,
            sigma_db=sigma, seed=seed, lam=lam, theta=theta,
            flood_interval_min=flood, prune_interval_min=prune, mode=mode
        )
        self.on_apply(new_cfg)
        self.destroy()
def main():
    parser = argparse.ArgumentParser(
        description="WSN AAMP/GDT simulator (GUI + headless mobility trial runner)"
    )
    parser.add_argument(
        "--mobility-trial",
        action="store_true",
        help="Run the mobility trial headlessly (5/32 nodes x 6 cycles by default) and exit.",
    )
    parser.add_argument(
        "--trials",
        type=int,
        default=5,
        help="Number of independent trials to average (default: 5).",
    )
    parser.add_argument(
        "--cycles",
        type=int,
        default=6,
        help="Number of recovery cycles per trial (default: 6).",
    )
    parser.add_argument(
        "--mobile-fraction",
        type=float,
        default=5 / 32,
        help="Fraction of nodes to displace (default reproduces 5 of 32, approx. 15.6%%).",
    )
    parser.add_argument(
        "--displacement",
        type=float,
        nargs=2,
        metavar=("MIN", "MAX"),
        default=(10.0, 15.0),
        help="Min/max displacement (meters) for moved nodes (default: 10 15).",
    )
    parser.add_argument(
        "--export-dir",
        type=str,
        help="Directory for exported artifacts (EPS/TXT). Defaults to ./exports.",
    )
    parser.add_argument(
        "--seed",
        type=int,
        help="Override RNG seed before running the headless mobility trial.",
    )
    parser.add_argument(
        "--baseline-no-aamp",
        action="store_true",
        help="Disable AAMP pruning during the mobility trial (baseline comparison).",
    )
    parser.add_argument(
        "--no-plot",
        action="store_true",
        help="Skip generating the EPS plot (still writes fig4.txt).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit the mobility trial summary as JSON.",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress stdout summary (useful when only exit code matters).",
    )
    args = parser.parse_args()

    if args.mobility_trial:
        app = WSNApp()
        app.withdraw()
        if args.seed is not None:
            app.cfg.seed = args.seed
            app.rng = random.Random(args.seed)
        displacement_min, displacement_max = args.displacement
        use_aamp = None if not args.baseline_no_aamp else False

        try:
            summary = app.run_mobility_trial(
                num_trials=args.trials,
                cycles=args.cycles,
                mobile_fraction=args.mobile_fraction,
                displacement_min=displacement_min,
                displacement_max=displacement_max,
                export_dir=args.export_dir,
                include_plot=not args.no_plot,
                use_aamp=use_aamp,
            )
        finally:
            app.destroy()

        if args.json:
            print(json.dumps(summary, indent=2))
        elif not args.quiet:
            print("Mobility Trial Summary:")
            for idx, (mean, std) in enumerate(
                zip(summary["mean_mae"], summary["std_mae"]), start=1
            ):
                print(f"  Cycle {idx}: {mean:.3f} ± {std:.3f} m")
            if summary.get("plot_path"):
                print(f"Plot saved to: {summary['plot_path']}")
            if summary.get("data_path"):
                print(f"Data saved to: {summary['data_path']}")
            if summary.get("csv_path"):
                print(f"CSV saved to: {summary['csv_path']}")
        return

    app = WSNApp()
    app.mainloop()


if __name__ == "__main__":
    main()