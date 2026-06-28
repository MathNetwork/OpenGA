/**
 * Reference View — pure functions for the simplicial graph visualization.
 *
 * Every astrolabe entry becomes a node.
 * Every ref relationship becomes a directed link (source → target).
 * Color by degree, size inversely proportional to degree.
 */
import type { SimulationNodeDatum, SimulationLinkDatum } from 'd3'
import { getSortFill, parseSortFromRecord } from './sortColors'

// ── Force graph types ──

export interface ForceNode extends SimulationNodeDatum {
    id: string
    name: string
    sort: string
    color: string
    radius: number
    degree?: number
    cluster?: number
    state?: string
}

export interface ForceLink extends SimulationLinkDatum<ForceNode> {
    id: string
    source: ForceNode | string
    target: ForceNode | string
    color: string
    dashed?: boolean
}

// ── Degree radius ──

export function degreeRadius(degree: number, baseRadius: number = 12): number {
  return Math.max(4, baseRadius - degree * 1.5)
}

// ── Ref view types ──

export interface RefViewNode {
  id: string
  degree: number
  stage: number
  name?: string
  sort?: string
  color: string
  radius: number
}

export interface RefViewLink {
  source: string
  target: string
  position: number
}

// ── Builders ──

export function buildRefViewNodes(
  rawNodes: { id: string; degree: number; stage: number; record?: string; name?: string; sort?: string }[],
): RefViewNode[] {
  return rawNodes.map(n => {
    const sort = n.record ? parseSortFromRecord(n.record) : (n.sort || '')
    return {
      id: n.id,
      degree: n.degree,
      stage: n.stage,
      name: n.name,
      sort: sort,
      color: getSortFill(sort),
      radius: degreeRadius(n.degree),
    }
  })
}

export function buildRefViewLinks(
  rawLinks: { source: string; target: string; position: number }[],
): RefViewLink[] {
  return rawLinks.map(l => ({
    source: l.source,
    target: l.target,
    position: l.position,
  }))
}

// ── Hit testing ──

export function hitTestNode(nodes: ForceNode[], x: number, y: number): ForceNode | null {
    let best: ForceNode | null = null
    let bestDist = Infinity
    for (const node of nodes) {
        if (node.x == null || node.y == null) continue
        const dx = node.x - x
        const dy = node.y - y
        const dist = Math.sqrt(dx * dx + dy * dy)
        if (dist <= node.radius && dist < bestDist) {
            best = node
            bestDist = dist
        }
    }
    return best
}

export function hitTestEdge(links: ForceLink[], x: number, y: number, threshold: number): ForceLink | null {
    let best: ForceLink | null = null
    let bestDist = Infinity
    for (const link of links) {
        const s = link.source as ForceNode
        const t = link.target as ForceNode
        if (s.x == null || s.y == null || t.x == null || t.y == null) continue
        const dist = pointToSegmentDist(x, y, s.x, s.y, t.x, t.y)
        if (dist <= threshold && dist < bestDist) {
            best = link
            bestDist = dist
        }
    }
    return best
}

function pointToSegmentDist(px: number, py: number, x1: number, y1: number, x2: number, y2: number): number {
    const dx = x2 - x1
    const dy = y2 - y1
    const lenSq = dx * dx + dy * dy
    if (lenSq === 0) return Math.sqrt((px - x1) ** 2 + (py - y1) ** 2)
    let t = ((px - x1) * dx + (py - y1) * dy) / lenSq
    t = Math.max(0, Math.min(1, t))
    const projX = x1 + t * dx
    const projY = y1 + t * dy
    return Math.sqrt((px - projX) ** 2 + (py - projY) ** 2)
}

// ── Physics mapping ──

export function mapPhysicsToD3(physics: {
    gravity: number
    repulsion: number
    linkDistance: number
    friction: number
}): {
    centerStrength: number
    manyBodyStrength: number
    linkDistance: number
    velocityDecay: number
} {
    return {
        centerStrength: Math.max(0, Math.min(1, physics.gravity / 100)),
        manyBodyStrength: -Math.abs(physics.repulsion) * 2,
        linkDistance: Math.max(10, physics.linkDistance * 2.5),
        velocityDecay: Math.max(0.05, Math.min(0.95, physics.friction / 100)),
    }
}

// ── Collapse geometry ──

export function computeCollapseTarget(
  ref: string[],
  nodePositions: Record<string, { x: number; y: number }>,
): { x: number; y: number } {
  let sumX = 0, sumY = 0, count = 0
  for (const h of ref) {
    const pos = nodePositions[h]
    if (pos) { sumX += pos.x; sumY += pos.y; count++ }
  }
  if (count === 0) return { x: 0, y: 0 }
  return { x: sumX / count, y: sumY / count }
}
