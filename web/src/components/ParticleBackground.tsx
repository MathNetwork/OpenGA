'use client'

import { useEffect, useRef } from 'react'

interface Particle {
  x: number
  y: number
  vx: number
  vy: number
  size: number
  color: string
  opacity: number
}

interface ParticleBackgroundProps {
  particleCount?: number
  mouseRadius?: number
}

// Astrolabe color palette
const colors = [
  '#be1420',   // red
  '#669aba',   // steel blue
  '#fbf0d9',   // cream
  '#ffffff',   // white
  '#a8d4f0',   // light blue
  '#ff9f43',   // orange
  '#ffcc80',   // light orange
  '#7ec8e3',   // sky blue
]

export default function ParticleBackground({
  particleCount = 80,
  mouseRadius = 200,
}: ParticleBackgroundProps) {
  const canvasRef = useRef<HTMLCanvasElement>(null)
  const mouseRef = useRef({ x: -1000, y: -1000 })
  const particlesRef = useRef<Particle[]>([])
  const animationRef = useRef<number | null>(null)

  useEffect(() => {
    const canvas = canvasRef.current
    if (!canvas) return

    const ctx = canvas.getContext('2d')
    if (!ctx) return

    const resizeCanvas = () => {
      canvas.width = window.innerWidth
      canvas.height = window.innerHeight
    }
    resizeCanvas()
    window.addEventListener('resize', resizeCanvas)

    const initParticles = () => {
      particlesRef.current = []
      for (let i = 0; i < particleCount; i++) {
        particlesRef.current.push({
          x: Math.random() * canvas.width,
          y: Math.random() * canvas.height,
          vx: (Math.random() - 0.5) * 0.4,
          vy: (Math.random() - 0.5) * 0.4,
          size: Math.random() * 1.5 + 0.8,
          color: colors[Math.floor(Math.random() * colors.length)],
          opacity: Math.random() * 0.3 + 0.7,
        })
      }
    }
    initParticles()

    const handleMouseMove = (e: MouseEvent) => {
      mouseRef.current = { x: e.clientX, y: e.clientY }
    }
    const handleMouseLeave = () => {
      mouseRef.current = { x: -1000, y: -1000 }
    }

    // Touch events for mobile
    const handleTouchMove = (e: TouchEvent) => {
      if (e.touches.length > 0) {
        const touch = e.touches[0]
        mouseRef.current = { x: touch.clientX, y: touch.clientY }
      }
    }
    const handleTouchEnd = () => {
      mouseRef.current = { x: -1000, y: -1000 }
    }

    window.addEventListener('mousemove', handleMouseMove)
    window.addEventListener('mouseleave', handleMouseLeave)
    window.addEventListener('touchstart', handleTouchMove, { passive: true })
    window.addEventListener('touchmove', handleTouchMove, { passive: true })
    window.addEventListener('touchend', handleTouchEnd)

    const animate = () => {
      ctx.clearRect(0, 0, canvas.width, canvas.height)

      const particles = particlesRef.current
      const mouse = mouseRef.current

      // Use smaller radius on mobile for less dense connections
      const isMobile = canvas.width < 768
      const effectiveRadius = isMobile ? mouseRadius * 0.7 : mouseRadius

      // Calculate mouse distance for each particle
      const mouseDistances: number[] = []
      particles.forEach((p) => {
        const mouseDx = p.x - mouse.x
        const mouseDy = p.y - mouse.y
        mouseDistances.push(Math.sqrt(mouseDx * mouseDx + mouseDy * mouseDy))
      })

      particles.forEach((p, i) => {
        p.x += p.vx
        p.y += p.vy

        if (p.x < 0 || p.x > canvas.width) p.vx *= -1
        if (p.y < 0 || p.y > canvas.height) p.vy *= -1

        p.x = Math.max(0, Math.min(canvas.width, p.x))
        p.y = Math.max(0, Math.min(canvas.height, p.y))

        const mouseDistance = mouseDistances[i]

        // Smoothly interpolate size and opacity based on distance
        // influence: 1 at center, 0 at edge, with smooth falloff
        const influence = mouseDistance < effectiveRadius
          ? Math.pow(1 - mouseDistance / effectiveRadius, 1.5)  // smooth cubic falloff
          : 0

        const minSize = p.size * 0.5
        const maxSize = p.size * 1.8
        const displaySize = minSize + (maxSize - minSize) * influence

        const minOpacity = p.opacity * 0.7
        const maxOpacity = p.opacity
        const displayOpacity = minOpacity + (maxOpacity - minOpacity) * influence

        ctx.beginPath()
        ctx.arc(p.x, p.y, displaySize, 0, Math.PI * 2)
        ctx.fillStyle = p.color
        ctx.globalAlpha = displayOpacity
        ctx.fill()
        ctx.globalAlpha = 1

        if (mouseDistance < effectiveRadius) {
          // Smooth quadratic falloff for line opacity
          const lineOpacity = Math.pow(1 - mouseDistance / effectiveRadius, 2) * (isMobile ? 0.4 : 0.5)
          ctx.beginPath()
          ctx.moveTo(p.x, p.y)
          ctx.lineTo(mouse.x, mouse.y)
          ctx.strokeStyle = '#fbf0d9'
          ctx.globalAlpha = lineOpacity
          ctx.lineWidth = 0.5 + lineOpacity * 1.5  // line width also fades
          ctx.stroke()
          ctx.globalAlpha = 1

          particles.forEach((p2, j) => {
            if (i >= j) return
            const p2MouseDistance = mouseDistances[j]

            if (p2MouseDistance < effectiveRadius) {
              const dx = p.x - p2.x
              const dy = p.y - p2.y
              const distance = Math.sqrt(dx * dx + dy * dy)

              // On mobile, only draw lines between closer particles
              const maxLineDistance = isMobile ? effectiveRadius * 0.6 : effectiveRadius

              if (distance < maxLineDistance) {
                // Combined influence: both particles' proximity to mouse affects line
                const avgInfluence = (
                  Math.pow(1 - mouseDistance / effectiveRadius, 2) +
                  Math.pow(1 - p2MouseDistance / effectiveRadius, 2)
                ) / 2
                const distanceFactor = Math.pow(1 - distance / maxLineDistance, 1.5)
                const opacity = avgInfluence * distanceFactor * (isMobile ? 0.3 : 0.35)

                ctx.beginPath()
                ctx.moveTo(p.x, p.y)
                ctx.lineTo(p2.x, p2.y)
                ctx.strokeStyle = '#669aba'
                ctx.globalAlpha = opacity
                ctx.lineWidth = 0.3 + opacity * 1.5
                ctx.stroke()
                ctx.globalAlpha = 1
              }
            }
          })
        }
      })

      animationRef.current = requestAnimationFrame(animate)
    }
    animate()

    return () => {
      window.removeEventListener('resize', resizeCanvas)
      window.removeEventListener('mousemove', handleMouseMove)
      window.removeEventListener('mouseleave', handleMouseLeave)
      window.removeEventListener('touchstart', handleTouchMove)
      window.removeEventListener('touchmove', handleTouchMove)
      window.removeEventListener('touchend', handleTouchEnd)
      if (animationRef.current) {
        cancelAnimationFrame(animationRef.current)
      }
    }
  }, [particleCount, mouseRadius])

  return (
    <canvas
      ref={canvasRef}
      className="absolute inset-0 pointer-events-none"
      style={{ background: 'transparent' }}
    />
  )
}
